package main

import (
	"fmt"
	"github.com/dedis/lago/bigint"
	"github.com/dedis/lago/polynomial"
	"github.com/dedis/lago/ring"
)

func main() {

	//d := uint32(1)
	//n := uint32(1)
	//m := uint32(0)
	//w := uint32(1)

	//q := bigint.NewIntFromString("8865920799731713")
	//q := bigint.NewIntFromString("257")
	//q := bigint.NewIntFromString("2147221513")
	//q := bigint.NewIntFromString("65537")
	//SetSettings(d, n, m, w, 4, *q, 8, 0, true)

	d := uint32(256)
	n := uint32(4)
	m := uint32(8)
	w := uint32(44)
	//q := bigint.NewIntFromString("4294962689") // 2^32 - 2^12 - 2^9 + 1
	q := bigint.NewIntFromString("65537")
	SetSettings(d, n, m, w, w, 4, *q, 1, 10, false)
	LinearEquationArgument_plus_Test()

	//CRTPackIntTest()
	//MintTest_plus()

	//RingMatAddTest()
	//RingMatMulTest()
	//RingMatScalarMulTest()
	//RingMatIsEqualTest()
	//ConvertIntToRingBitsTest()
	//MulPolyTest()
	//RingMulTest()

	//RqRandomTest()
	//HashTest()
	//SamMatTest()
	//CommitmentTest()
	//MintTest()
	//BinaryCommitTest()
	//BalanceProofTest()
	//LinearEquationArgumentTest()
	//OneOutOfManyProofTest()
	//LinearSumProofTest()

	//GenerateDeltaTest()
	//MakePijTest()
}

func LinearSumProofTest() {
	N := 9
	beta := uint32(2)
	k := uint32(3)
	l := uint32(5)

	r := new(ring.Ring)
	r.N = settings.d
	r.Q = settings.q
	r.Poly, _ = polynomial.NewPolynomial(settings.d, settings.q, settings.nttParams)

	va := beta
	vb := k*va + settings.m
	Ga, _ := SamMat(va, 0)
	Gb, _ := SamMat(vb, 0)

	DebugPrint("Ga", Ga)
	DebugPrint("Gb", Gb)

	Pv := make([]RingMartix, N)
	rv := make([]RingMartix, N)

	zero, _ := NewRingMartix(beta, 1, settings.nttParams)
	zero.SetZeroRingMartix(r, settings.d)

	for i := 0; i < N; i++ {
		Pu, pr, _ := Commitment(Ga, zero, 10)
		Pv[i] = *Pu
		rv[i] = *pr

		DebugPrint("Pu"+fmt.Sprint(i), Pv[i])
		DebugPrint("pr"+fmt.Sprint(i), rv[i])
	}

	ComB, f, zb, zr, Ev, x, _ := LinearSumProof(Ga, Gb, &rv[l], l, k, beta, Pv, 20, 14)
	result, _ := LinearSumVerify(Ga, Gb, ComB, f, zb, zr, Pv, Ev, x)

	fmt.Printf("%v\n", result)
}

func LinearEquationArgumentTest() {
	va := settings.precision
	vb := 4*va + settings.m
	Ga, _ := SamMat(va, 0)
	Gb, _ := SamMat(vb, 0)

	Av := make([]RingMartix, 1)
	amtin := make([]RingMartix, 1)
	rav := make([]RingMartix, 1)
	Avtmp, ratmp, amttmp, _ := Mint(Ga, uint64(2))
	Av[0] = *Avtmp
	if ratmp != nil {
		rav[0] = *ratmp
	}
	amtin[0] = *amttmp

	vout := make([]uint64, 2)
	vout[0] = uint64(1)
	vout[1] = uint64(1)

	ComE, f, g, z, zg, Bv, zbv, x, _ := LinearEquationArgument(Ga, Gb, Av, amtin, rav, vout, 20, 14, 2)
	result, _ := LinearEquationVerify(Ga, Gb, ComE, f, g, z, zg, x, Av, Bv, zbv)

	fmt.Printf("%v\n", result)
}

func OneOutOfManyProofTest() {
	N := 9
	beta := uint32(2)
	k := uint32(3)
	l := uint32(5)

	r := new(ring.Ring)
	r.N = settings.d
	r.Q = settings.q
	r.Poly, _ = polynomial.NewPolynomial(settings.d, settings.q, settings.nttParams)

	va := beta
	vb := 2*k*va + settings.m
	Ga, _ := SamMat(va, 0)
	Gb, _ := SamMat(vb, 0)

	DebugPrint("Ga", Ga)
	DebugPrint("Gb", Gb)

	Pv := make([]RingMartix, N)
	rv := make([]RingMartix, N)

	zero, _ := NewRingMartix(beta, 1, settings.nttParams)
	zero.SetZeroRingMartix(r, settings.d)

	for i := 0; i < N; i++ {
		Pu, pr, _ := Commitment(Ga, zero, 10)
		Pv[i] = *Pu
		rv[i] = *pr

		DebugPrint("Pu"+fmt.Sprint(i), Pv[i])
		DebugPrint("pr"+fmt.Sprint(i), rv[i])
	}

	ComB, f, zb, zr, Ev, x, _ := OneOutOfManyProof(Ga, Gb, &rv[l], l, k, beta, Pv, 20, 14)

	result, _ := OneOutOfManyVerify(Ga, Gb, ComB, f, zb, zr, Pv, Ev, x)

	fmt.Printf("%v\n", result)
}

func BalanceProofTest() {
	va := settings.precision + settings.m
	vb := 6*va - 2 + settings.m
	Ga, _ := SamMat(va, 0)
	Gb, _ := SamMat(vb, 0)

	Av := make([]RingMartix, 1)
	amtin := make([]RingMartix, 1)
	Avtmp, _, amttmp, _ := Mint(Ga, uint64(2))
	Av[0] = *Avtmp
	amtin[0] = *amttmp

	vout := make([]uint64, 2)
	vout[0] = uint64(1)
	vout[1] = uint64(1)

	ComB, ComC, f, zb, zc, Bv, zoutv, x, _ := BalanceProof(Ga, Gb, Av, amtin, vout, 20, 14, 2)
	result, _ := BalanceVerify(Ga, Gb, ComB, ComC, f, zb, zc, Av, Bv, zoutv, x)

	fmt.Printf("%v\n", result)
}

func RqRandomTest() {
	var i uint32
	r := RqRandomB(0, settings.d, settings.B, false)

	for i = 0; i < settings.d; i++ {
		fmt.Printf("%v\n", r[i])
	}
}

func HashTest() {
	r1 := new(ring.Ring)
	r1.N = settings.d
	r1.Q = settings.q
	r1.Poly, _ = polynomial.NewPolynomial(settings.d, settings.q, nil)

	r2 := new(ring.Ring)
	r2.N = settings.d
	r2.Q = settings.q
	r2.Poly, _ = polynomial.NewPolynomial(settings.d, settings.q, nil)

	msg := make([]byte, 2)
	msg[0] = 'M'
	msg[1] = 'G'

	Hash(msg, r1)
	Hash(msg, r2)

	cor1 := r1.Poly.GetCoefficients()
	cor2 := r1.Poly.GetCoefficients()
	for i := range cor1 {
		if !cor1[i].EqualTo(&cor2[i]) {
			fmt.Printf("false")
			return
		}
	}

	fmt.Printf("true")
}

func ConvertIntToRingBitsTest() {
	d := uint32(64)
	q := bigint.NewIntFromString("129")
	balance := uint64(9223372036854775807)
	result, _ := ConvertIntToRingBits(balance, d, settings.precision, *q, nil)
	for i := 0; i < 64; i++ {
		bit := result.ringvectors[i].rings[0].Poly.GetCoefficients()
		fmt.Printf("%v\n", bit[0])
	}
}

func SamMatTest() {
	v := uint32(1)
	G, _ := SamMat(v, 0)
	fmt.Printf("%v\n", G.ringvectors[0].rings[0].Poly.GetCoefficients()[0])
	fmt.Printf("%v\n", G.ringvectors[G.col-1].rings[G.row-1].Poly.GetCoefficients()[settings.d-1])
}

func CommitmentTest() {
	v := uint32(2)
	r := new(ring.Ring)
	r.N = settings.n
	r.Q = settings.q
	r.Poly, _ = polynomial.NewPolynomial(settings.d, settings.q, settings.nttParams)
	coeffs := make([]bigint.Int, settings.d)
	coeffs[0].SetInt(int64(1))

	G, _ := SamMat(v, 0)
	msg, _ := NewRingMartix(v, 1, settings.nttParams)

	var i uint32
	for i = 0; i < v; i++ {
		tmp, _ := ring.CopyRing(r)
		_ = tmp.Poly.SetCoefficients(coeffs)
		msg.ringvectors[i].rings[0] = *tmp
	}

	com, rnd, _ := Commitment(G, msg, -1)
	fmt.Printf("%v\n", com.ringvectors[com.col-1].rings[0].Poly.GetCoefficients())
	for i = 0; i < rnd.col; i++ {
		fmt.Printf("%v\n", rnd.ringvectors[i].rings[0].Poly.GetCoefficients())
	}
}

func MintTest() {
	amt := uint64(5)
	coeffs := make([]bigint.Int, settings.d)
	coeffs[0].SetInt(int64(1))

	bits, _ := ConvertIntToRingBits(amt, settings.d, settings.precision, settings.q, settings.nttParams)
	G, _ := SamMat(settings.precision, 0)
	B, r, mbits, _ := Mint(G, amt)

	y, _ := ring.CopyRing(&G.ringvectors[0].rings[0])
	_ = y.Poly.SetCoefficients(coeffs)

	fmt.Printf("%v\n", Open(G, B, bits, r, y))
	fmt.Printf("%v\n", mbits.RingMatIsEqual(bits))
}

func BinaryCommitTest() {
	amt := uint64(5)
	coeffs := make([]bigint.Int, settings.d)
	coeffs[0].SetInt(int64(1))

	bits, _ := ConvertIntToRingBits(amt, settings.d, settings.precision, settings.q, settings.nttParams)
	G, _ := SamMat(64*2, 0)
	A, B, ra, rb, a, _ := BinaryCommit(G, bits, 100, 10)
	fmt.Printf("%v\n", A.ringvectors[0].rings[0].Poly.GetCoefficients())
	fmt.Printf("%v\n\n", A.ringvectors[A.col-1].rings[0].Poly.GetCoefficients())
	fmt.Printf("%v\n", B.ringvectors[0].rings[0].Poly.GetCoefficients())
	fmt.Printf("%v\n\n", B.ringvectors[B.col-1].rings[0].Poly.GetCoefficients())
	fmt.Printf("%v\n", ra.ringvectors[0].rings[0].Poly.GetCoefficients())
	fmt.Printf("%v\n\n", ra.ringvectors[ra.col-1].rings[0].Poly.GetCoefficients())
	fmt.Printf("%v\n", rb.ringvectors[0].rings[0].Poly.GetCoefficients())
	fmt.Printf("%v\n\n", rb.ringvectors[rb.col-1].rings[0].Poly.GetCoefficients())
	fmt.Printf("%v\n", a.ringvectors[0].rings[0].Poly.GetCoefficients())
	fmt.Printf("%v\n", a.ringvectors[a.col-1].rings[0].Poly.GetCoefficients())
}

func RingMatAddTest() {
	col := uint32(3)
	row := uint32(2)
	n := uint32(4)
	var q *bigint.Int
	q = bigint.NewIntFromString("2000")
	//nttParams := polynomial.GenerateNTTParams(n, *q)

	r := new(ring.Ring)
	r.N = n
	r.Q = *q
	r.Poly, _ = polynomial.NewPolynomial(n, *q, nil)
	coeffs := make([]bigint.Int, n)
	coeffs[0].SetInt(int64(1))
	coeffs[1].SetInt(int64(2))
	coeffs[2].SetInt(int64(3))

	m, _ := NewRingMartix(col, row, nil)
	var i, j uint32
	for i = 0; i < col; i++ {
		for j = 0; j < row; j++ {
			tmp, _ := ring.CopyRing(r)
			_ = tmp.Poly.SetCoefficients(coeffs)
			m.ringvectors[i].rings[j] = *tmp
		}
	}
	_, _ = m.RingMatAdd(m, m)
	fmt.Printf("%v\n", m.ringvectors[0].rings[0].Poly.GetCoefficients())
	fmt.Printf("%v\n", m.ringvectors[0].rings[1].Poly.GetCoefficients())
	fmt.Printf("%v\n", m.ringvectors[1].rings[0].Poly.GetCoefficients())
	fmt.Printf("%v\n", m.ringvectors[1].rings[1].Poly.GetCoefficients())
	fmt.Printf("%v\n", m.ringvectors[2].rings[0].Poly.GetCoefficients())
	fmt.Printf("%v\n", m.ringvectors[2].rings[1].Poly.GetCoefficients())
}

func RingMatMulTest() {
	one := uint32(2)
	two := uint32(3)
	n := uint32(2)
	var q *bigint.Int
	q = bigint.NewIntFromString("97")
	nttParams := polynomial.GenerateNTTParams(n, *q)

	r := new(ring.Ring)
	r.N = n
	r.Q = *q
	r.Poly, _ = polynomial.NewPolynomial(n, *q, nttParams)
	coeffs := make([]bigint.Int, n)

	m1, _ := NewRingMartix(one, two, nttParams)
	m2, _ := NewRingMartix(two, one, nttParams)
	m, _ := NewRingMartix(one, one, nttParams)
	var i, j uint32
	for i = 0; i < one; i++ {
		for j = 0; j < two; j++ {
			tmp1, _ := ring.CopyRing(r)
			tmp2, _ := ring.CopyRing(r)
			coeffs[0].SetInt(int64(98))
			_ = tmp1.Poly.SetCoefficients(coeffs)
			coeffs[0].SetInt(int64(3))
			_ = tmp2.Poly.SetCoefficients(coeffs)

			m1.ringvectors[i].rings[j] = *tmp1
			m2.ringvectors[j].rings[i] = *tmp2
		}
	}
	for i = 0; i < one; i++ {
		for j = 0; j < one; j++ {
			tmp, _ := ring.CopyRing(r)
			m.ringvectors[i].rings[j] = *tmp
		}
	}
	_, _ = m.RingMatMul(m1, m2)
	for i = 0; i < one; i++ {
		for j = 0; j < one; j++ {
			fmt.Printf("%v\n", m.ringvectors[i].rings[j].Poly.GetCoefficients())
		}
	}
}

func RingMatScalarMulTest() {
	col := uint32(64)
	row := uint32(1)
	n := uint32(64)
	var q *bigint.Int
	q = bigint.NewIntFromString("257")
	nttParams := polynomial.GenerateNTTParams(n, *q)

	r := new(ring.Ring)
	r.N = n
	r.Q = *q
	r.Poly, _ = polynomial.NewPolynomial(n, *q, nttParams)
	coeffs := make([]bigint.Int, n)
	coeffs[0].SetInt(int64(1))
	_ = r.Poly.SetCoefficients(coeffs)

	m, _ := NewRingMartix(col, row, nttParams)
	var i, j, k uint32
	for i = 0; i < col; i++ {
		for j = 0; j < row; j++ {
			tmp, _ := ring.CopyRing(r)
			for k = 0; k < n; k++ {
				coeffs[k].SetInt(int64(k + 50))
			}

			_ = tmp.Poly.SetCoefficients(coeffs)

			m.ringvectors[i].rings[j] = *tmp
		}
	}

	fmt.Printf("%v\n\n", r.Poly.GetCoefficients())

	for i = 0; i < m.col; i++ {
		for j = 0; j < m.row; j++ {
			fmt.Printf("%v\n", m.ringvectors[i].rings[j].Poly.GetCoefficients())
		}
	}
	fmt.Printf("\n")
	_, _ = m.RingMatScalarMul(r, m)
	for i = 0; i < m.col; i++ {
		for j = 0; j < m.row; j++ {
			fmt.Printf("%v\n", m.ringvectors[i].rings[j].Poly.GetCoefficients())
		}
	}
}

func MulPolyTest() {
	n := uint32(64)
	var q *bigint.Int
	q = bigint.NewIntFromString("257")
	nttParams := polynomial.GenerateNTTParams(n, *q)

	r := new(ring.Ring)
	r.N = n
	r.Q = *q
	r.Poly, _ = polynomial.NewPolynomial(n, *q, nttParams)
	coeffs := make([]bigint.Int, n)
	coeffs[0].SetInt(int64(1))
	_ = r.Poly.SetCoefficients(coeffs)

	var i uint32
	for i = 0; i < n; i++ {
		coeffs[i].SetInt(int64(i + 50))
	}

	tmp, _ := ring.CopyRing(r)
	_ = tmp.Poly.SetCoefficients(coeffs)

	fmt.Printf("%v\n\n", tmp.Poly.GetCoefficients())
	_, _ = tmp.MulPoly(tmp, r)
	fmt.Printf("%v\n\n", tmp.Poly.GetCoefficients())
}

func RingMatIsEqualTest() {
	one := uint32(1)
	two := uint32(2)
	n := uint32(4)
	var q *bigint.Int
	q = bigint.NewIntFromString("97")

	coeffs := make([]bigint.Int, n)
	coeffs[0].SetInt(int64(2))

	r := new(ring.Ring)
	r.N = n
	r.Q = *q
	r.Poly, _ = polynomial.NewPolynomial(n, *q, nil)

	m, _ := NewRingMartix(one, two, nil)
	t, _ := NewRingMartix(one, two, nil)
	var i, j uint32
	for i = 0; i < one; i++ {
		for j = 0; j < two; j++ {
			tmp, _ := ring.CopyRing(r)
			_ = tmp.Poly.SetCoefficients(coeffs)

			m.ringvectors[i].rings[j] = *tmp
		}
	}

	for i = 0; i < one; i++ {
		for j = 0; j < two; j++ {
			tmp, _ := ring.CopyRing(r)
			_ = tmp.Poly.SetCoefficients(coeffs)

			t.ringvectors[i].rings[j] = *tmp
		}
	}

	fmt.Printf("%v\n", m.RingMatIsEqual(t))

	coeffs[0].SetInt(int64(1))
	_ = t.ringvectors[t.col-1].rings[t.row-1].Poly.SetCoefficients(coeffs)

	fmt.Printf("%v\n", t.RingMatIsEqual(m))
}

func RingMulTest() {
	coeffs := make([]bigint.Int, settings.d)

	tmp := new(ring.Ring)
	tmp.N = settings.d
	tmp.Q = settings.q
	tmp.Poly, _ = polynomial.NewPolynomial(settings.d, settings.q, settings.nttParams)

	coeffs[0].SetInt(int64(-1))
	_ = tmp.Poly.SetCoefficients(coeffs)

	tmp2, _ := ring.CopyRing(tmp)
	_ = tmp2.Poly.SetCoefficients(coeffs)

	r, _ := ring.CopyRing(tmp)
	_, _ = r.MulPoly(tmp, tmp2)
	fmt.Printf("%v\n", r.GetCoefficients())

	// there is bug in MulPoly to handle same inputs
	_, _ = r.MulPoly(tmp, tmp)
	fmt.Printf("%v\n", r.GetCoefficients())
}

func GenerateDeltaTest() {
	v := MakeDeltaMatrix(7, 2, 3)
	for i := range v {
		for j := range v[i].ringvectors {
			coeffs := v[i].ringvectors[j].rings[0].GetCoefficients()
			fmt.Printf("%v\n", coeffs[0])
		}
		fmt.Printf("\n")
	}

}

func MakePijTest() {
	r := new(ring.Ring)
	r.N = settings.d
	r.Q = settings.q
	r.Poly, _ = polynomial.NewPolynomial(settings.d, settings.q, settings.nttParams)

	coeffs := make([]bigint.Int, settings.d)
	a := make([]ring.Ring, 3)
	delta := make([]ring.Ring, 3)
	for i := range a {
		coeffs[0].SetInt(int64(i + 1))
		tmpring, _ := ring.CopyRing(r)
		_ = tmpring.Poly.SetCoefficients(coeffs)
		a[i] = *tmpring
		coeffs[0].SetInt(int64(i + 2))
		tmpring2, _ := ring.CopyRing(r)
		_ = tmpring2.Poly.SetCoefficients(coeffs)
		delta[i] = *tmpring2
	}

	piv := MakePij(a, delta)

	for i := range piv {
		cef := piv[i].Poly.GetCoefficients()
		fmt.Printf("%v\n", cef[0])
	}
}

func CRTPackIntTest() {
	amt := uint64(95)
	bvec, err := CRTPackInt(amt, settings.d, settings.precision, settings.q, settings.nttParams)

	if err != nil {
		fmt.Printf("error\n")
		return
	}
	ShowRing_plus(&bvec.ringvectors[0].rings[0], settings.d, settings.precision)
}

func MintTest_plus() {
	amt := uint64(5)
	coeffs := make([]bigint.Int, settings.d)
	coeffs[0].SetInt(int64(1))

	G, _ := SamMat_plus(0)
	B, r, mbits, _ := Mint_plus(G, amt)

	y, _ := ring.CopyRing(&G.ringvectors[0].rings[0])
	_ = y.Poly.SetCoefficients(coeffs)

	fmt.Printf("%v\n", UMCOpen(G, B, mbits, r, y))
	ShowRing_plus(&mbits.ringvectors[0].rings[0], settings.d, settings.precision)
}

func LinearEquationArgument_plus_Test() {
	M := 2

	r := new(ring.Ring)
	r.N = settings.d
	r.Q = settings.q
	r.Poly, _ = polynomial.NewPolynomial(settings.d, settings.q, settings.nttParams)

	coeffs := make([]bigint.Int, settings.d)
	zeta := make([]ring.Ring, M)
	Av := make([]RingMartix, M)
	amtin := make([]RingMartix, M)
	rav := make([]RingMartix, M)

	vout := make([]uint64, 1)

	UMC_G, _ := SamMat_plus(0)

	for i := 0; i < M; i++ {
		coeffs[0].SetInt(int64(i + 1))
		tmpring, _ := ring.CopyRing(r)
		_ = tmpring.Poly.SetCoefficients(coeffs)
		zeta[i] = *tmpring

		A, rbin, bin, _ := Mint_plus(UMC_G, uint64(i+1))
		amtin[i] = *bin
		rav[i] = *rbin
		Av[i] = *A
	}
	vout[0] = 3

	ComF, f, zg, z, Bv, zbv, x, err := LinearEquationArgument_plus(UMC_G, Av, amtin, rav, vout, 10, 1, 1, 1, 1)
	if err != nil {
		return
	}

	rst, err := LinearEquationVerify_plus(UMC_G, ComF, f, zg, z, x, Av, Bv, zbv)
	if err != nil {
		return
	}
	fmt.Printf("%v\n", rst)
}
