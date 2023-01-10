package main

import "C"
import (
	"crypto/md5"
	"encoding/binary"
	"errors"
	"fmt"
	"github.com/dedis/lago/bigint"
	"github.com/dedis/lago/polynomial"
	"github.com/dedis/lago/ring"
	"math/rand"
	"time"
)

type MartixSettings struct {
	// MatRiCT settings
	d, n, m, w, precision uint32
	q                     bigint.Int
	p, B                  int
	nttParams             *polynomial.NttParams
	debug                 bool

	// additional settings for MatRiCT+
	w_zeta uint32
}

var settings *MartixSettings

func DebugPrint(name string, data interface{}) {
	if settings.debug {
		coeffslen := settings.d
		fmt.Printf("------ [%v] ------\n", name)
		switch info := data.(type) {
		case *ring.Ring:
			ShowRing(info, coeffslen)
		case ring.Ring:
			ShowRing(&info, coeffslen)
		case []ring.Ring:
			ShowRingVector(info, coeffslen)
		case *RingMartix:
			info.ShowMatrix(coeffslen)
		case RingMartix:
			info.ShowMatrix(coeffslen)
		default:
			fmt.Printf("%v\n", info)
		}
	}
}

func SetSettings(d, n, m, w, w_zeta, precision uint32, q bigint.Int, p, B int, debug bool) *MartixSettings {
	nttParams := polynomial.GenerateNTTParams(d, q)
	settings = &MartixSettings{d, n, m, w, precision, q, p, B, nttParams, debug, w_zeta}
	return settings
}

// the naive implementation of H to return a ring in C_{w, p}^d
// the collision of this function is high, may consider a better mapping
func Hash(msg []byte, x *ring.Ring) {
	//high collision function, may consider better mapping
	hashed := md5.Sum(msg)
	var b = hashed[:8]
	seed := int64(binary.LittleEndian.Uint64(b))
	coeffs := make([]bigint.Int, settings.d)
	rand.Seed(seed)
	// get w different elements from d
	p := rand.Perm(int(settings.d))
	for _, loc := range p[:settings.w] {
		rnd := rand.Intn(2*settings.p + 1)
		rnd = rnd - settings.p
		coeffs[loc].SetInt(int64(rnd))
		coeffs[loc].Mod(&coeffs[loc], &settings.q)
	}

	// for testing
	//coeffs := make([]bigint.Int, settings.d)
	//coeffs[0].SetInt(1)
	//
	_ = x.Poly.SetCoefficients(coeffs)
	return
}

// zeta_i in C'
// || zeta_i ||_inf = 1, || zeta_i ||_1 = w_zeta
func BuildZeta(msg []byte, zeta []ring.Ring, r *ring.Ring) {
	hashed := md5.Sum(msg)
	var b = hashed[:8]
	seed := int64(binary.LittleEndian.Uint64(b))
	coeffs := make([]bigint.Int, settings.d)
	rand.Seed(seed)
	// get w different elements from d
	for i := 0; i < len(zeta); i++ {
		p := rand.Perm(int(settings.d))
		for _, loc := range p[:settings.w_zeta] {
			coeffs[loc].SetInt(int64(1))
		}
		tmpring, _ := ring.CopyRing(r)
		_ = tmpring.Poly.SetCoefficients(coeffs)
		zeta[i] = *tmpring
		seed++
		rand.Seed(seed)
	}

	// for test
	//coeffs := make([]bigint.Int, settings.d)
	//coeffs[0].SetInt(1)
	//tmpring, _ := ring.CopyRing(r)
	//_ = tmpring.Poly.SetCoefficients(coeffs)
	//zeta[0] = *tmpring

	return
}

// G size	: n * (m + v)
// r size	: m * 1
// msg size : v * 1
// Commitment function Com(msg; r) = G * (r, msg)
func Commitment(G, msg *RingMartix, bound int) (*RingMartix, *RingMartix, error) {
	if msg.row != 1 {
		return nil, nil, errors.New("m should be a v*1-size Rq vector")
	}
	if G.row < msg.col {
		return nil, nil, errors.New("G.row should >= msg.col")
	}

	// build r (we allow r == nil for test)
	nttParams := settings.nttParams
	m := G.row - msg.col
	r, _ := NewRingMartix(m, 1, nttParams)
	if r != nil {
		seed := time.Now().UnixNano() // may consider more secure seeds
		if bound < 0 {
			r.SetRandomQRingMartix(&G.ringvectors[0].rings[0], seed, settings.d, settings.q)
		} else {
			r.SetRandomBRingMartix(&G.ringvectors[0].rings[0], seed, settings.d, bound, false)
		}
	}

	com, err := CommitmentWithRandom(G, msg, r)
	return com, r, err
}

// Com(msg; r)
func CommitmentWithRandom(G, msg, r *RingMartix) (*RingMartix, error) {
	com, err := NewRingMartix(G.col, 1, settings.nttParams)
	if com == nil || err != nil {
		return nil, err
	}

	com.SetRingMartix(&G.ringvectors[0].rings[0])

	// rmsg  = (r, msg)
	rmsg, _ := NewRingMartix(G.row, 1, settings.nttParams)
	_, err = rmsg.RingMatCombine(r, msg)
	if err != nil {
		return nil, err
	}

	// com = G  * rmsg
	com, err = com.RingMatMul(G, rmsg)
	return com, err
}

// if y != nil	: Com(msg; r) =? y * G
// else			: Com(msg; r) =? G
func Open(G, com, msg, r *RingMartix, y *ring.Ring) bool {
	recom, err := CommitmentWithRandom(G, msg, r)
	if err != nil {
		return false
	}

	// com = y * com
	if y != nil {
		_, _ = com.RingMatScalarMul(y, com)
	}

	return com.RingMatIsEqual(recom)
}

// G = (G0, gm)
// G size	: n * m
// G0_size	: (n - 1) * m
// gm:		: 1 * m
// r size	: m
// msg size : 1
// Commitment function Com(msg; r) = G * (r, msg)
func UMCCom(G, msg *RingMartix, bound int) (*RingMartix, *RingMartix, error) {
	if msg.row != 1 || msg.col != 1 {
		return nil, nil, errors.New("m should be one Rq element")
	}

	// build r (we allow r == nil for test)
	nttParams := settings.nttParams
	m := G.row
	r, _ := NewRingMartix(m, 1, nttParams)
	if r != nil {
		seed := time.Now().UnixNano() // may consider more secure seeds
		if bound < 0 {
			r.SetRandomQRingMartix(&G.ringvectors[0].rings[0], seed, settings.d, settings.q)
		} else {
			r.SetRandomBRingMartix(&G.ringvectors[0].rings[0], seed, settings.d, bound, false)
		}
	}

	com, err := UMCComWithRandom(G, msg, r)
	return com, r, err
}

// UMC(m;r)
func UMCComWithRandom(G, msg, r *RingMartix) (*RingMartix, error) {
	com, err := NewRingMartix(G.col, 1, settings.nttParams)
	if com == nil || err != nil {
		return nil, err
	}

	com.SetRingMartix(&G.ringvectors[0].rings[0])

	com, err = com.RingMatMul(G, r)

	// zmsg  = (0, msg)
	zero, err := NewRingMartix(G.col-1, 1, settings.nttParams)
	if zero == nil {
		err = errors.New("NewRingMartix fail")
		return nil, err
	}
	zero.SetZeroRingMartix(&G.ringvectors[0].rings[0], settings.d)

	zmsg, err := NewRingMartix(G.col, 1, settings.nttParams)

	_, err = zmsg.RingMatCombine(zero, msg)
	if err != nil {
		return nil, err
	}

	// com = G  * rmsg
	com, err = com.RingMatAdd(com, zmsg)
	return com, err
}

// if y != nil	: Com(msg; r) =? y * G
// else			: Com(msg; r) =? G
func UMCOpen(G, com, msg, r *RingMartix, y *ring.Ring) bool {
	recom, err := UMCComWithRandom(G, msg, r)
	if err != nil {
		return false
	}

	// com = y * com
	if y != nil {
		_, _ = com.RingMatScalarMul(y, com)
	}

	return com.RingMatIsEqual(recom)
}

// SamMat function (Algorithm 1)
func SamMat(v uint32, seed int64) (*RingMartix, error) {
	m := settings.m
	n := settings.n
	nttParams := settings.nttParams
	d := settings.d
	q := settings.q

	row := m + v
	if n == 0 || row == 0 {
		return nil, errors.New("n, m+v should not be 0")
	}

	// r as a tmp ring on Rq = Zq[X] / [X^d + 1]
	r := new(ring.Ring)
	r.N = d
	r.Q = q
	r.Poly, _ = polynomial.NewPolynomial(d, q, nttParams)

	G, err := NewRingMartix(n, row, nttParams)
	if G == nil {
		return nil, errors.New("NewRingMartix fail")
	}

	G.SetRandomQRingMartix(r, seed, settings.d, settings.q)
	return G, err
}

func SamMat_plus(seed int64) (*RingMartix, error) {
	m := settings.m
	n := settings.n
	nttParams := settings.nttParams
	d := settings.d
	q := settings.q

	if n == 0 || m == 0 {
		return nil, errors.New("n, m should not be 0")
	}

	// r as a tmp ring on Rq = Zq[X] / [X^d + 1]
	r := new(ring.Ring)
	r.N = d
	r.Q = q
	r.Poly, _ = polynomial.NewPolynomial(d, q, nttParams)

	G, err := NewRingMartix(n, m, nttParams)
	if G == nil {
		return nil, errors.New("NewRingMartix fail")
	}

	G.SetRandomQRingMartix(r, seed, settings.d, settings.q)

	//for test
	//G.SetRandomBRingMartix(r, seed, settings.d, 1, false)
	//G.ShowMatrix(settings.d)
	return G, err
}

// Mint function (Algorithm 5)
func Mint(G *RingMartix, amt uint64) (cn, cnk, bits *RingMartix, err error) {
	bits, err = ConvertIntToRingBits(amt, settings.d, settings.precision, settings.q, settings.nttParams)
	cn, cnk, err = Commitment(G, bits, settings.B)
	return
}

// Mint function in MatRiCT+ (Algorithm 3)
func Mint_plus(G *RingMartix, amt uint64) (cn, cnk, vpack *RingMartix, err error) {
	vpack, _ = CRTPackInt(amt, settings.d, settings.precision, settings.q, settings.nttParams)
	cn, cnk, err = UMCCom(G, vpack, settings.B)
	return
}

// f = [f_0, ..., f_r-1]
// sum 2^i f_i =? 0
func CheckPackedf(f *RingMartix) bool {
	var i, j uint32
	delta := settings.d / settings.precision
	coeffs := f.ringvectors[0].rings[0].Poly.GetCoefficients()
	result := make([]bigint.Int, delta)
	zero := make([]bigint.Int, delta)

	for j = 0; j < delta; j++ {
		for i = 0; i < settings.precision; i++ {
			tmp := new(bigint.Int)
			tmp.Lsh(&coeffs[delta*i+j], i) // f_i * 2^i
			result[j].Add(&result[j], tmp)
		}
		result[j].Mod(&result[j], &settings.q)
		if !result[j].EqualTo(&zero[j]) {
			return false
		}
	}
	return true
}

// BinaryCommit function (not for delta) (Algorithm 6)
// t s_j-dimensional binary vector is regarded as an (sum s_j)*1 matrix b
// G is an n*(2*(m+2v))-size matrix
// Ba and Bra are bounds of a and ra
func BinaryCommit(G, b *RingMartix, Ba, Bra int) (A, B, ra, rb, a *RingMartix, err error) {
	nttParams := settings.nttParams
	seed := time.Now().UnixNano() // may consider more secure seeds

	// build a
	a, err = NewRingMartix(b.col, 1, nttParams)
	if a == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	a.SetRandomBRingMartix(&b.ringvectors[0].rings[0], seed, settings.d, Ba, true)

	A, B, ra, rb, err = BinaryCommitWithA(G, a, b, Ba, Bra)
	return
}

// deltav and av: k-many (beta*1)-size delta vectors
func CommitForDelta(G *RingMartix, deltav []RingMartix, Bdelta, Brdelta int, isbinary bool) (A, B, ra, rb, a, delta *RingMartix, av []RingMartix, err error) {
	nttParams := settings.nttParams
	seed := time.Now().UnixNano() // may consider more secure seeds

	k := len(deltav)
	av = make([]RingMartix, k)

	// build av
	for i := 0; i < k; i++ {
		atmp, _ := NewRingMartix(deltav[0].col, 1, nttParams)
		if atmp == nil {
			err = errors.New("NewRingMartix fail")
			return
		}
		atmp.SetRandomRingMartixForDelta(&deltav[0].ringvectors[0].rings[0], seed, settings.d, Bdelta)
		seed = time.Now().UnixNano() + 1 // may consider more secure seeds
		av[i] = *atmp
	}

	// delta = (deltav[0], ..., deltav[k - 1])
	delta, err = NewRingMartix(uint32(k)*deltav[0].col, 1, nttParams)
	if delta == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	delta.col = 0 // a _trick_ to make RingMatCombine work when i = 0

	// a = (av[0], ..., av[k - 1])
	a, err = NewRingMartix(uint32(k)*deltav[0].col, 1, nttParams)
	if a == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	a.col = 0 // a _trick_ to make RingMatCombine work when i = 0

	for i := 0; i < k; i++ {
		_, _ = delta.RingMatCombine(delta, &deltav[i])
		_, _ = a.RingMatCombine(a, &av[i])
	}

	if isbinary {
		A, B, ra, rb, err = BinaryCommitWithA(G, a, delta, Bdelta, Brdelta)
	} else {
		B, rb, err = Commitment(G, delta, settings.B)
		A, ra, err = Commitment(G, a, Brdelta)
	}

	return
}

// binary commitment when a is set
func BinaryCommitWithA(G, a, b *RingMartix, Ba, Bra int) (A, B, ra, rb *RingMartix, err error) {
	nttParams := settings.nttParams

	// build c
	c, err := NewRingMartix(b.col, 1, nttParams)
	if c == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	c.SetRingMartix(&b.ringvectors[0].rings[0])

	coeffs := make([]bigint.Int, settings.d)
	coeffs[0].SetInt(int64(1))
	onering, _ := ring.CopyRing(&b.ringvectors[0].rings[0])
	_ = onering.Poly.SetCoefficients(coeffs)

	nonering, _ := ring.CopyRing(onering)
	coeffs[0].SetInt(int64(-1))
	_ = nonering.Poly.SetCoefficients(coeffs)

	ntworing, _ := ring.CopyRing(onering)
	coeffs[0].SetInt(int64(-2))
	_ = ntworing.Poly.SetCoefficients(coeffs)

	// c = (-2 * b + 1) * a
	_, err = c.RingMatScalarMul(ntworing, b)
	_, err = c.RingMatScalarAdd(onering, c)
	_, err = c.RingMatHadamardProd(c, a)

	// build d
	d, err := NewRingMartix(b.col, 1, nttParams)
	if d == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	d.SetRingMartix(&b.ringvectors[0].rings[0])

	// d = 0 - a^2
	_, err = d.RingMatHadamardProd(a, a)
	_, err = d.RingMatScalarMul(nonering, d)

	// bc = (b, c)
	bc, err := NewRingMartix(b.col+c.col, 1, nttParams)
	if bc == nil {
		err = errors.New("NewRingMartix fail")
		return
	}

	_, err = bc.RingMatCombine(b, c)
	B, rb, err = Commitment(G, bc, settings.B)

	// ad = (a, d)
	ad, err := NewRingMartix(a.col+d.col, 1, nttParams)
	if ad == nil {
		err = errors.New("NewRingMartix fail")
		return
	}

	_, err = ad.RingMatCombine(a, d)
	A, ra, err = Commitment(G, ad, Bra)

	return
}

// generate corrector values
func Corrector(amtin, amtout []RingMartix) (*RingMartix, error) {
	var i uint32
	nttParams := settings.nttParams
	c, err := NewRingMartix(amtin[0].col-1, 1, nttParams)
	if c == nil {
		return nil, err
	}

	coeffs := make([]bigint.Int, settings.d)

	for i = 0; i < c.col; i++ {
		tmpring, _ := ring.CopyRing(&amtin[0].ringvectors[0].rings[0])
		_ = tmpring.Poly.SetCoefficients(coeffs)
		for j := range amtout {
			_, err = tmpring.Add(tmpring, &amtout[j].ringvectors[i].rings[0])
		}

		for j := range amtin {
			_, _ = tmpring.Sub(tmpring, &amtin[j].ringvectors[i].rings[0])
		}

		if i != 0 {
			_, _ = tmpring.Add(tmpring, &c.ringvectors[i-1].rings[0])
		}

		_, _ = tmpring.Div(tmpring, *bigint.NewInt(2))
		c.ringvectors[i].rings[0] = *tmpring
	}

	return c, nil
}

// convert i to the k-size representation of base beta
func ConvertToBase(i, k, beta uint32) []uint32 {
	var j uint32
	tmp := i
	iv := make([]uint32, k)
	for j = 0; j < k; j++ {
		iv[j] = tmp % beta
		tmp = tmp / beta
	}
	return iv
}

// make len * 1 size delta vector with for l (l < len)
// beta^k = N
// delta: len * 1
func MakeDeltaVector(l, len uint32) (*RingMartix, error) {
	var i uint32
	r := new(ring.Ring)
	r.N = settings.d
	r.Q = settings.q
	nttParams := settings.nttParams
	r.Poly, _ = polynomial.NewPolynomial(settings.d, settings.q, nttParams)
	one := make([]bigint.Int, settings.d)
	one[0].SetInt(int64(1))

	delta, err := NewRingMartix(len, 1, nttParams)
	if delta == nil {
		return nil, err
	}

	for i = 0; i < delta.col; i++ {
		tmpring, _ := ring.CopyRing(r)
		if i == l {
			_ = tmpring.Poly.SetCoefficients(one)
		}

		delta.ringvectors[i].rings[0] = *tmpring
	}

	return delta, err
}

// generate delta vector
// beta^k = N
// deltav: k-many len*1 size
func MakeDeltaMatrix(l, k, beta uint32) []RingMartix {
	var i uint32
	// make the base beta representation of l
	deltav := make([]RingMartix, k)
	tmp := l
	for i = 0; i < k; i++ {
		delta, _ := MakeDeltaVector(tmp%beta, beta)
		deltav[i] = *delta
		tmp = tmp / beta
	}

	return deltav
}

// (a + b * x) * (c_0 + c_1 * x + ... + c_{k-1} * x^{k-1})
// when c = nil, return c = [a, b]
func LinearMulPoly(a, b *ring.Ring, c []ring.Ring, k int) {
	// directly returning c = [a, b] to avoid setting c[0] = 1 in iterated multiplication
	if k == 0 {
		atmp, _ := ring.CopyRing(a)
		_ = atmp.Poly.SetCoefficients(a.Poly.GetCoefficients())
		c[0] = *atmp
		if len(c) > 1 {
			btmp, _ := ring.CopyRing(b)
			_ = btmp.Poly.SetCoefficients(b.Poly.GetCoefficients())
			c[1] = *btmp
		}
		return
	}

	// c_{k+1} = b * c_k (the last one is dropped)
	tmpring, _ := ring.CopyRing(&c[0])
	if k < len(c)-1 {
		_, _ = tmpring.MulPoly(b, &c[k])
		c[k+1] = *tmpring
	}

	// c_i = b * c_{i-1} + a * c_i
	for i := k; i > 0; i-- {
		tmp, _ := ring.CopyRing(tmpring)
		_, _ = tmp.MulPoly(b, &c[i-1])
		_, _ = c[i].MulPoly(a, &c[i])
		_, _ = c[i].Add(tmp, &c[i])
	}

	// c_0 = a * c_0
	_, _ = c[0].MulPoly(a, &c[0])
}

// prod_{j = 0}^{k - 1} (x * delta_{l_j, i_j} + a_{j, i_j})
func MakePij(a, delta []ring.Ring) []ring.Ring {
	k := len(a)
	piv := make([]ring.Ring, k)
	for i := 0; i < k; i++ {
		LinearMulPoly(&a[i], &delta[i], piv, i)
	}
	return piv
}

// E_j = sum_i p_{i, j} * P_i + Com(0; rho_j)
// P	: N * 1
// pv	: N * k
func MakeEj(G *RingMartix, pv [][]ring.Ring, P []RingMartix, beta uint32) (Ev, rhov []RingMartix, err error) {
	N := len(P)
	k := len(pv[0])

	Ev = make([]RingMartix, k)
	rhov = make([]RingMartix, k)

	zero, err := NewRingMartix(beta, 1, settings.nttParams)
	if zero == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	zero.SetZeroRingMartix(&P[0].ringvectors[0].rings[0], settings.d)
	for j := 0; j < k; j++ {
		// Com(0; rho_j)
		Com0, rhoj, _ := Commitment(G, zero, settings.B)
		Ej, _ := NewRingMartix(P[0].col, P[0].row, settings.nttParams)
		if Ej == nil {
			err = errors.New("NewRingMartix fail")
			return
		}
		Ej.SetZeroRingMartix(&P[0].ringvectors[0].rings[0], settings.d)

		for i := 0; i < N; i++ {
			tmp, _ := NewRingMartix(P[0].col, P[0].row, settings.nttParams)
			if tmp == nil {
				err = errors.New("NewRingMartix fail")
				return
			}
			tmp.SetRingMartix(&pv[0][0])
			_, _ = tmp.RingMatScalarMul(&pv[i][j], &P[i])
			_, _ = Ej.RingMatAdd(Ej, tmp)
		}
		_, _ = Ej.RingMatAdd(Ej, Com0)

		Ev[j] = *Ej
		if rhoj != nil {
			rhov[j] = *rhoj
		}
	}

	return
}

// zr = x^k * r - sum_j x^j * rho_j
func ComputeZr(x *ring.Ring, r *RingMartix, rhov []RingMartix) (zr *RingMartix, err error) {
	xtmp, _ := ring.CopyRing(x)
	coeffs := make([]bigint.Int, settings.d)
	coeffs[0].SetInt(int64(1))
	err = xtmp.Poly.SetCoefficients(coeffs)

	zr, err = NewRingMartix(rhov[0].col, rhov[0].row, settings.nttParams)
	if zr == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	zr.SetZeroRingMartix(&rhov[0].ringvectors[0].rings[0], settings.d)

	for i := 0; i < len(rhov); i++ {
		tmp, _ := NewRingMartix(rhov[0].col, rhov[0].row, settings.nttParams)
		if tmp == nil {
			err = errors.New("NewRingMartix fail")
			return
		}
		tmp.SetRingMartix(x)
		// tmp = xtmp * rhov[i]
		_, _ = tmp.RingMatScalarMul(xtmp, &rhov[i])
		// zr = zr + tmp
		_, _ = zr.RingMatAdd(zr, tmp)
		// xtmp = xtmp * x
		_, _ = xtmp.MulPoly(xtmp, x)
	}

	tmp, _ := NewRingMartix(rhov[0].col, rhov[0].row, settings.nttParams)
	if tmp == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	tmp.SetRingMartix(x)
	// tmp = xtmp * r
	_, _ = tmp.RingMatScalarMul(xtmp, r)
	// zr = tmp - zr
	_, _ = zr.RingMatSub(tmp, zr)

	return
}
