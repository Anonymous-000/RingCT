package main

import "C"
import (
	"errors"
	"fmt"
	"github.com/dedis/lago/bigint"
	"github.com/dedis/lago/ring"
)

// the balance proof part of Algorithm 8 and 9
// Only works when M = 1 and S <= 2 as range proofs of corrector values are embedded in binary proofs
// Ga		: the n*(v+m)-size matrix for Com(c-2c) and v_i
// Gb		: the n*(2*(vout.len+1)*v-2+m)-size matrix for BinaryCommit
// Av		: the commitment of inputs as A_in
// amtin	: is the M-many matrix for input amount (bits)
// amtout	: is the S-many output amounts (uint32)
func BalanceProof(Ga, Gb *RingMartix, Av, amtin []RingMartix, vout []uint64, Ba, Bra, Brd int) (ComB, ComC, f, zb, zc *RingMartix, Bv, zoutv []RingMartix, x *ring.Ring, err error) {
	var i uint32
	nttParams := settings.nttParams
	S := uint32(len(vout))
	M := uint32(len(amtin))
	if S > 2 || M > 1 {
		err = errors.New("only support 1 input and <= 2 outputs")
		return
	}

	// mint coins for outputs
	Bv = make([]RingMartix, S)
	rbv := make([]RingMartix, S)
	vbits := make([]RingMartix, S)

	// build out = (vbits_0, ..., vbits_{S-1})
	out, err := NewRingMartix(S * amtin[0].col, 1, nttParams)
	if out == nil {
		err = errors.New("only support 1 input and <= 2 outputs")
		return
	}
	out.col = 0 // a _trick_ to make RingMatCombine work when i = 0

	for i = 0; i < S; i++ {
		Bvtmp, rbvtmp, vbitstmp, _ := Mint(Ga, vout[i])
		Bv[i] = *Bvtmp
		if rbvtmp != nil {
			rbv[i] = *rbvtmp
		}
		vbits[i] = *vbitstmp

		_, err = out.RingMatCombine(out, vbitstmp)
	}

	// build corrector values
	c, err := Corrector(amtin, vbits)

	//A, B, Corr, D, ra, rb, a, rc, rd, err := BalanceProofI(Ga, Gb, out, c, Ba, Bra)
	ComA, ComB, ComC, ComD, ra, rb, a, rc, rd, Gv, rgv, err := BalanceProofI(Ga, Gb, out, c, Ba, Bra, Brd)

	msg := append(ComA.ToBytes(), ComB.ToBytes()...)
	msg = append(msg, ComC.ToBytes()...)
	msg = append(msg, ComD.ToBytes()...)
	for i = 0; i < M; i++ {
		msg = append(msg, Av[i].ToBytes()...)
	}
	for i = 0; i < S; i++ {
		msg = append(msg, Bv[i].ToBytes()...)
		msg = append(msg, Gv[i].ToBytes()...)
	}

	x, err = ring.CopyRing(&Ga.ringvectors[0].rings[0])
	Hash(msg, x)

	f, zb, zc, zoutv, err = BalanceProofII(x, out, c, a, rb, ra, rc, rd, rbv, rgv)
	return
}

// the balance proof part 1, Algorithm 9 (excluding hash and mint)
// amtout is (S * 64) * 1-size matrix
func BalanceProofI(Ga, Gb, amtout, c *RingMartix, Ba, Bra, Brd int) (A, B, C, D, ra, rb, a, rc, rd *RingMartix, Gv, rgv []RingMartix, err error) {
	var i, j uint32
	// outc = (amtout, c)
	nttParams := settings.nttParams
	outc, err := NewRingMartix(amtout.col + c.col, 1, nttParams)
	if outc == nil {
		return
	}

	_, err = outc.RingMatCombine(amtout, c)
	A, B, ra, rb, a, err = BinaryCommit(Gb, outc, Ba, Bra)

	// Compute G_i's and r_g^(i)'s
	S := (a.col + 1) / settings.precision - 1
	Gv = make([]RingMartix, S)
	rgv = make([]RingMartix, S)
	ai, err := NewRingMartix(settings.precision, 1, nttParams)
	if ai == nil {
		err = errors.New("NewRingMartix fail")
		return
	}

	for i = 0; i < S; i++ {
		for j = 0; j < ai.col; j++ {
			ai.ringvectors[j].rings = a.ringvectors[i * settings.precision + j].rings
		}

		Gtmp, rgtmp, _ := Commitment(Ga, ai, Brd)
		Gv[i] = *Gtmp
		if rgtmp != nil {
			rgv[i] = *rgtmp
		}
	}

	// get a_c in a
	ac, err := NewRingMartix(c.col, 1, nttParams)
	if ac == nil {
		return
	}
	for i = 0; i < ac.col; i++ {
		ac.ringvectors[i].rings = a.ringvectors[i + amtout.col].rings
	}

	// build c_i - 2 * c_{i + 1} and a_{c, i} - 2 * a_{c, i + 1} from c and a_c
	// c_0 = c_r = a_{c, 0} = a_{c, r} = 0
	coeffs := make([]bigint.Int, settings.d)
	zeroring, _ := ring.CopyRing(&c.ringvectors[0].rings[0])
	_ = zeroring.Poly.SetCoefficients(coeffs)
	tworing, _ := ring.CopyRing(zeroring)
	coeffs[0].SetInt(int64(2))
	_ = tworing.Poly.SetCoefficients(coeffs)

	a2a, err := NewRingMartix(ac.col + 1, 1, nttParams)
	if a2a == nil {
		return
	}

	c2c, err := NewRingMartix(c.col + 1, 1, nttParams)
	if c2c == nil {
		return
	}

	for i = 0; i < a2a.col; i++ {
		atmpring, _ := ring.CopyRing(zeroring)
		ctmpring, _ := ring.CopyRing(zeroring)
		if i == a2a.col - 1 {
			// 2 * a_{c, r} = 2 * c_r = 0
			_ = atmpring.Poly.SetCoefficients(zeroring.Poly.GetCoefficients())
			_ = ctmpring.Poly.SetCoefficients(zeroring.Poly.GetCoefficients())
		} else {
			_, err = atmpring.MulPoly(tworing, &ac.ringvectors[i].rings[0])
			_, err = ctmpring.MulPoly(tworing, &c.ringvectors[i].rings[0])
		}

		if i == 0 {
			_, err = atmpring.Sub(zeroring, atmpring)
			_, err = ctmpring.Sub(zeroring, ctmpring)
		} else {
			_, err = atmpring.Sub(&ac.ringvectors[i - 1].rings[0], atmpring)
			_, err = ctmpring.Sub(&c.ringvectors[i - 1].rings[0], ctmpring)
		}

		a2a.ringvectors[i].rings[0] = *atmpring
		c2c.ringvectors[i].rings[0] = *ctmpring
	}

	C, rc, err = Commitment(Ga, c2c, settings.B)
	D, rd, err = Commitment(Ga, a2a, Brd)

	return
}

// the balance proof part 2, Algorithm 10 (rejection sampling is ignored)
func BalanceProofII(x *ring.Ring, amtout, c, a, rb, ra, rc, rd *RingMartix, rbv, rgv []RingMartix) (f, zb, zc *RingMartix, zoutv []RingMartix, err error) {
	// TODO: verify the bound of f, zb, zc, and g
	var i uint32
	nttParams := settings.nttParams

	// build f
	f, err = NewRingMartix(a.col, 1, nttParams)
	if f == nil {
		return
	}
	// f_{out, i} = x * amtout_i + a_{out, i}
	for i = 0; i < amtout.col; i++ {
		tmpring, _ := ring.CopyRing(x)
		_, _ = tmpring.MulPoly(x, &amtout.ringvectors[i].rings[0])
		_, _ = tmpring.Add(tmpring, &a.ringvectors[i].rings[0])
		f.ringvectors[i].rings[0] = *tmpring
	}
	// f_{c, i} = x * c_i + a_{c, i}
	for i = 0; i < c.col; i++ {
		tmpring, _ := ring.CopyRing(x)
		_, _ = tmpring.MulPoly(x, &c.ringvectors[i].rings[0])
		_, _ = tmpring.Add(tmpring, &a.ringvectors[i + amtout.col].rings[0])
		f.ringvectors[i + amtout.col].rings[0] = *tmpring
	}

	// build g
	g, err := NewRingMartix(a.col, 1, nttParams)
	if g == nil {
		return
	}
	// g = f * (x - f)
	for i = 0; i < g.col; i++ {
		tmpring, _ := ring.CopyRing(x)
		_, _ = tmpring.Sub(x, &f.ringvectors[i].rings[0])
		_, _ = tmpring.MulPoly(tmpring, &f.ringvectors[i].rings[0])
		g.ringvectors[i].rings[0] = *tmpring
	}

	// build zb
	if rb != nil {
		zb, err = NewRingMartix(rb.col, 1, nttParams)
		if zb == nil {
			return
		}
		// zb = x * rb + ra
		_ = zb.SetRingMartix(x)
		_, err = zb.RingMatScalarMul(x, rb)
		_, err = zb.RingMatAdd(zb, ra)
	}

	// build zc
	if rc != nil {
		zc, err = NewRingMartix(rc.col, 1, nttParams)
		if zc == nil {
			return
		}
		// zc = x * rc + rd
		_ = zc.SetRingMartix(x)
		_, err = zc.RingMatScalarMul(x, rc)
		_, err = zc.RingMatAdd(zc, rd)
	}

	// build zg^(i)'s
	S := uint32(len(rbv))
	zoutv = make([]RingMartix, S)
	for i = 0; i < S; i++ {
		if &rgv[i] != nil && &rbv[i] != nil {
			tmp, _ := NewRingMartix(rbv[i].col, 1, nttParams)
			if tmp == nil {
				return
			}
			// zg = x * rb + rg
			_ = tmp.SetRingMartix(x)
			_, err = tmp.RingMatScalarMul(x, &rbv[i])
			_, err = tmp.RingMatAdd(tmp, &rgv[i])
			zoutv[i] = *tmp
		}
	}

	return
}

// the balance proof verification part of Algorithm 10
func BalanceVerify(Ga, Gb, ComB, ComC, f, zb, zc *RingMartix, Av, Bv, zoutv []RingMartix, x *ring.Ring) (result bool, err error) {
	// TODO: verify the bound of f, zb, zc, and g
	var i, j uint32
	nttParams := settings.nttParams
	result = false

	// build g
	g, err := NewRingMartix(f.col, 1, nttParams)
	if g == nil {
		return
	}
	// g = f * (x - f)
	for i = 0; i < g.col; i++ {
		tmpring, _ := ring.CopyRing(x)
		_, _ = tmpring.Sub(x, &f.ringvectors[i].rings[0])
		_, _ = tmpring.MulPoly(tmpring, &f.ringvectors[i].rings[0])
		g.ringvectors[i].rings[0] = *tmpring
	}

	// A = Com(f, g; zb) - x * B
	fg, err := NewRingMartix(f.col + g.col, 1, nttParams)
	if fg == nil {
		return
	}
	_, err = fg.RingMatCombine(f, g)
	Comfg, err := CommitmentWithRandom(Gb, fg, zb)

	xB, err := NewRingMartix(ComB.col, ComB.row, nttParams)
	if xB == nil {
		return
	}
	_ = xB.SetRingMartix(x)
	_, err = xB.RingMatScalarMul(x, ComB)
	ComA, err := xB.RingMatSub(Comfg, xB)

	// get f_c in f
	S := uint32(len(Bv))
	fcsize := (f.col + 1) / (S + 1) - 1 // should be v - 1 = 63
	offset := S * (fcsize + 1)			// should be v * S = 64 * S
	fc, err := NewRingMartix(fcsize, 1, nttParams)
	if fc == nil {
		return
	}
	for i = 0; i < fc.col; i++ {
		fc.ringvectors[i].rings = f.ringvectors[i + offset].rings
	}

	coeffs := make([]bigint.Int, settings.d)
	zeroring, _ := ring.CopyRing(&f.ringvectors[0].rings[0])
	_ = zeroring.Poly.SetCoefficients(coeffs)
	tworing, _ := ring.CopyRing(zeroring)
	coeffs[0].SetInt(int64(2))
	_ = tworing.Poly.SetCoefficients(coeffs)

	// f2f_{i} = f_{c, i} - 2 * f_{c, i + 1}
	f2f, err := NewRingMartix(fc.col + 1, 1, nttParams)
	if f2f == nil {
		return
	}

	for i = 0; i < f2f.col; i++ {
		ftmpring, _ := ring.CopyRing(zeroring)
		if i == f2f.col - 1 {
			// 2 * f_{c, r} = 0
			_ = ftmpring.Poly.SetCoefficients(zeroring.Poly.GetCoefficients())
		} else {
			_, err = ftmpring.MulPoly(tworing, &fc.ringvectors[i].rings[0])
		}

		if i == 0 {
			_, err = ftmpring.Sub(zeroring, ftmpring)
		} else {
			_, err = ftmpring.Sub(&fc.ringvectors[i - 1].rings[0], ftmpring)
		}

		f2f.ringvectors[i].rings[0] = *ftmpring
	}

	// D = Com(fcf; zc) - x * C
	ComF, err := CommitmentWithRandom(Ga, f2f, zc)
	xC, err := NewRingMartix(ComC.col, ComC.row, nttParams)
	if xC == nil {
		return
	}
	_ = xC.SetRingMartix(x)
	_, err = xC.RingMatScalarMul(x, ComC)
	ComD, err := xC.RingMatSub(ComF, xC)

	// rebuild G_i's
	Gv := make([]RingMartix, S)
	fi, err := NewRingMartix(settings.precision, 1, nttParams)
	if fi == nil {
		err = errors.New("NewRingMartix fail")
		return
	}

	for i = 0; i < S; i++ {
		// get f_out^(i)'s
		for j = 0; j < fi.col; j++ {
			fi.ringvectors[j].rings = f.ringvectors[i * settings.precision + j].rings
		}
		ComFtmp, _ := CommitmentWithRandom(Ga, fi, &zoutv[i])

		// G_i = Com(f_out^(i), zg_i) - x * cnk_i
		xCnk, _ := NewRingMartix(ComFtmp.col, ComFtmp.row, nttParams)
		if xCnk == nil {
			return
		}
		_ = xCnk.SetRingMartix(x)
		_, err = xCnk.RingMatScalarMul(x, &Bv[i])
		ComG, _ := xCnk.RingMatSub(ComFtmp, xCnk)
		Gv[i] = *ComG
	}

	// rebuild xverify and text xverify =? x
	msg := append(ComA.ToBytes(), ComB.ToBytes()...)
	msg = append(msg, ComC.ToBytes()...)
	msg = append(msg, ComD.ToBytes()...)
	for i := range Av {
		msg = append(msg, Av[i].ToBytes()...)
	}
	for i := range Bv {
		msg = append(msg, Bv[i].ToBytes()...)
		msg = append(msg, Gv[i].ToBytes()...)
	}
	xverify, err := ring.CopyRing(x)
	Hash(msg, xverify)

	cor1 := x.Poly.GetCoefficients()
	cor2 := xverify.Poly.GetCoefficients()
	for i := range cor1 {
		if !cor1[i].EqualTo(&cor2[i]) {
			return
		}
	}

	result = true
	return
}

// the one-out-of-many proof part of Algorithm 8 and 9
// N = beta^k = len(P)
// Ga	: the n*(beta+m)-size matrix for Com(0; rho_i)
// Gb	: the n*(2*k*beta+m) is for BinaryCommitForDelta
func OneOutOfManyProof(Ga, Gb, r *RingMartix,l, k, beta uint32, P []RingMartix, Bdelta, Brdelta int) (B, f, zb, zr *RingMartix, Ev []RingMartix, x *ring.Ring, err error) {
	var i, j uint32
	nttParams := settings.nttParams
	N := uint32(len(P))

	deltav := MakeDeltaMatrix(l, k, beta)
	A, B, ra, rb, a, delta, av, err := CommitForDelta(Gb, deltav, Bdelta, Brdelta, true)

	DebugPrint("a", a)

	// pv is N * k size
	pv := make([][]ring.Ring, N)

	for i = 0; i < N; i++ {
		aiv := make([]ring.Ring, k)
		deltaiv := make([]ring.Ring, k)
		iv := ConvertToBase(i, k, beta)
		for j = 0; j < k; j++ {
			aiv[j] = av[j].ringvectors[iv[j]].rings[0]
			deltaiv[j] = deltav[j].ringvectors[iv[j]].rings[0]
		}

		pv[i] = MakePij(aiv, deltaiv)

		DebugPrint("pv" + fmt.Sprint(i), pv[i])
	}

	Ev, rhov, err := MakeEj(Ga, pv, P, beta)

	for i := range Ev {
		DebugPrint("Ev" + fmt.Sprint(i), Ev[i])
		DebugPrint("rhov" + fmt.Sprint(i), rhov[i])
	}

	// x = Hash(A, B, (P_i), (Ev_i))
	msg := append(A.ToBytes(), B.ToBytes()...)
	for i = 0; i < N; i++ {
		msg = append(msg, P[i].ToBytes()...)
	}
	for i = 0; i < k; i++ {
		msg = append(msg, Ev[i].ToBytes()...)
	}

	x, err = ring.CopyRing(&Ga.ringvectors[0].rings[0])
	Hash(msg, x)

	// f = x * delta + a
	f, err = NewRingMartix(delta.col, 1, nttParams)
	if f == nil {
		return
	}
	for i = 0; i < f.col; i++ {
		tmpring, _ := ring.CopyRing(x)
		_, _ = tmpring.MulPoly(x, &delta.ringvectors[i].rings[0])
		_, _ = tmpring.Add(tmpring, &a.ringvectors[i].rings[0])
		f.ringvectors[i].rings[0] = *tmpring
	}

	DebugPrint("f", f)

	// zb = x * rb + ra
	if rb != nil {
		zb, err = NewRingMartix(rb.col, 1, nttParams)
		if zb == nil {
			return
		}
		for i = 0; i < zb.col; i++ {
			tmpring, _ := ring.CopyRing(x)
			_, _ = tmpring.MulPoly(x, &rb.ringvectors[i].rings[0])
			_, _ = tmpring.Add(tmpring, &ra.ringvectors[i].rings[0])
			zb.ringvectors[i].rings[0] = *tmpring
		}
	}

	// zr = x^k * r - sum_j x^j * rho_j
	zr, err = ComputeZr(x, r, rhov)

	DebugPrint("zr", zr)

	// Ev = Ev_1, ..., Ev_{k - 1}
	// E0 = &Ev[0]
	Ev = Ev[1:]
	return
}

func OneOutOfManyVerify(Ga, Gb, ComB, f, zb, zr *RingMartix, P, Ev []RingMartix, x *ring.Ring) (result bool, err error) {
	// TODO: verify the bound
	var i, j uint32
	nttParams := settings.nttParams
	result = false
	k := uint32(len(Ev)) + 1
	beta := f.col / k
	N := uint32(len(P))

	// build g
	g, err := NewRingMartix(f.col, 1, nttParams)
	if g == nil {
		return
	}
	// g = f * (x - f)
	for i = 0; i < g.col; i++ {
		tmpring, _ := ring.CopyRing(x)
		_, _ = tmpring.Sub(x, &f.ringvectors[i].rings[0])
		_, _ = tmpring.MulPoly(tmpring, &f.ringvectors[i].rings[0])
		g.ringvectors[i].rings[0] = *tmpring
	}

	// A = Com(f, g; zb) - x * B
	fg, err := NewRingMartix(f.col + g.col, 1, nttParams)
	if fg == nil {
		return
	}
	_, err = fg.RingMatCombine(f, g)
	Comfg, err := CommitmentWithRandom(Gb, fg, zb)

	xB, err := NewRingMartix(ComB.col, ComB.row, nttParams)
	if xB == nil {
		return
	}
	_ = xB.SetRingMartix(x)
	_, err = xB.RingMatScalarMul(x, ComB)
	ComA, err := xB.RingMatSub(Comfg, xB)

	// sum_i f_{j, i} =? x
	for j = 0; j < k; j++ {
		coeffs := make([]bigint.Int, settings.d)
		tmpring, _ := ring.CopyRing(x)
		_ = tmpring.Poly.SetCoefficients(coeffs)

		for i = 0; i < beta; i++ {
			_, _ = tmpring.Add(tmpring, &f.ringvectors[j * beta + i].rings[0])
		}

		cor1 := x.Poly.GetCoefficients()
		cor2 := tmpring.Poly.GetCoefficients()
		for colen := range cor1 {
			if !cor1[colen].EqualTo(&cor2[colen]) {
				return
			}
		}
	}

	// E_0 = sum_i (prod_j f_{j, i_j} * P_i)
	E0, err := NewRingMartix(ComB.col, ComB.row, nttParams)
	if E0 == nil {
		return
	}
	_ = E0.SetZeroRingMartix(x, settings.d)

	for i = 0; i < N; i++ {
		coeffs := make([]bigint.Int, settings.d)
		coeffs[0].SetInt(1)
		tmpring, _ := ring.CopyRing(x)
		_ = tmpring.Poly.SetCoefficients(coeffs)
		iv := ConvertToBase(i, k, beta)

		for j = 0; j < k; j++ {
			_, _ = tmpring.MulPoly(tmpring, &f.ringvectors[j * beta + iv[j]].rings[0])
		}

		DebugPrint("prod_j f_{j," + fmt.Sprint(i) + "_j}", tmpring)

		// tmp = tmpring * P[i]
		tmp, _ := NewRingMartix(ComB.col, ComB.row, nttParams)
		if tmp == nil {
			return
		}
		_ = tmp.SetRingMartix(x)
		_, _ = tmp.RingMatScalarMul(tmpring, &P[i])

		_, _ = E0.RingMatAdd(tmp, E0)
	}

	DebugPrint("sum_i fi*Pi", E0)

	// E_0 = sum_{j = 1}^{k - 1} x^j * E_j - Com(0; zr)
	zero, err := NewRingMartix(beta, 1, settings.nttParams)
	if zero == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	zero.SetZeroRingMartix(x, settings.d)
	Com0, err := CommitmentWithRandom(Ga, zero, zr)
	_, _ = E0.RingMatSub(E0, Com0)

	DebugPrint("Com0", Com0)
	DebugPrint("fiPi - Com0", E0)

	// E_0 = E_0 - sum_{j = 1}^{k - 1} E_j * x^j
	xtmp, _ := ring.CopyRing(x)
	err = xtmp.Poly.SetCoefficients(x.Poly.GetCoefficients())

	for i = 0; i < k - 1; i++ {
		tmp, _ := NewRingMartix(Ev[0].col, Ev[0].row, settings.nttParams)
		if tmp == nil {
			err = errors.New("NewRingMartix fail")
			return
		}
		tmp.SetRingMartix(x)
		// tmp = xtmp * Ev[i]
		_, _ = tmp.RingMatScalarMul(xtmp, &Ev[i])
		// E0 = E0 - tmp
		_, _ = E0.RingMatSub(E0, tmp)
		// xtmp = xtmp * x
		_, _ = xtmp.MulPoly(xtmp, x)
	}

	DebugPrint("E0", E0)

	// x = Hash(A, B, (P_i), (Ev_i))
	msg := append(ComA.ToBytes(), ComB.ToBytes()...)
	for i := 0; i < len(P); i++ {
		msg = append(msg, P[i].ToBytes()...)
	}
	msg = append(msg, E0.ToBytes()...)
	for i := 0; i < len(Ev); i++ {
		msg = append(msg, Ev[i].ToBytes()...)
	}

	xverify, err := ring.CopyRing(&Ga.ringvectors[0].rings[0])
	Hash(msg, xverify)

	cor1 := x.Poly.GetCoefficients()
	cor2 := xverify.Poly.GetCoefficients()
	for colen := range cor1 {
		if !cor1[colen].EqualTo(&cor2[colen]) {
			return
		}
	}

	result = true
	return
}