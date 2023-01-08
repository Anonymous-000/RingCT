package main

import (
	"errors"
	"fmt"
	"github.com/dedis/lago/bigint"
	"github.com/dedis/lago/ring"
	"time"
)

// the linear equation argument
// Only works when w_0 = ... = w_{S-1} = 1 and w_S = ... = w_{M+S-1} = -1 (i.e., balance proof)
// Ga		: the n * v-size matrix for commitment of c, t, and amtout_i's
// Gb		: the n * (2 * vout.len * v) is for BinaryCommit
// Av		: the commitment of inputs as A_in
// amtin	: is the M-many matrix for input amount bits
// vout 	: is the S-many output amounts (uint32)
func LinearEquationArgument(Ga, Gb *RingMartix, Av, amtin, rav []RingMartix, vout []uint64, Bt, Bd, Brd int) (ComE, f, g, z, zg *RingMartix, Bv, zbv []RingMartix, x *ring.Ring, err error) {
	var i uint32
	S := uint32(len(vout))
	M := uint32(len(amtin))

	ComD, ComE, ComF, rt, rb, b, c, d, t, rd, Bv, Gv, rbv, rtv, err := LinearEquationArgumentI(Ga, Gb, amtin, vout, Bt, Bd, Brd)

	// x = Hash(D, E, F, Av, (B_i, G_i))
	msg := append(ComD.ToBytes(), ComE.ToBytes()...)
	msg = append(msg, ComF.ToBytes()...)
	for i = 0; i < M; i++ {
		msg = append(msg, Av[i].ToBytes()...)
	}
	for i = 0; i < S; i++ {
		msg = append(msg, Bv[i].ToBytes()...)
		msg = append(msg, Gv[i].ToBytes()...)
	}

	x, err = ring.CopyRing(&Ga.ringvectors[0].rings[0])
	Hash(msg, x)

	f, g, z, zg, zbv, err = LinearEquationArgumentII(x, b, t, c, d, rd, rb, rt, rav, rbv, rtv)

	return
}

// Algorithm 2 prover's side before receiving x
func LinearEquationArgumentI(Ga, Gb *RingMartix, amtin []RingMartix, vout []uint64, Bt, Bd, Brd int) (ComD, ComE, ComF, rt, rb, b, c, d, t, rd *RingMartix, Bv, Gv, rbv, rtv []RingMartix, err error) {
	var i, j uint32
	nttParams := settings.nttParams
	S := uint32(len(vout))
	M := uint32(len(amtin))

	// mint coins for outputs
	Bv = make([]RingMartix, S)
	rbv = make([]RingMartix, S)
	amtout := make([]RingMartix, S)

	// build b = (amtout_0, ..., amtout_{S-1})
	b, err = NewRingMartix(S*amtin[0].col, 1, nttParams)
	if b == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	b.col = 0 // a _trick_ to make RingMatCombine work when i = 0

	for i = 0; i < S; i++ {
		Btmp, rbtmp, outtmp, _ := Mint(Ga, vout[i])
		Bv[i] = *Btmp
		if rbtmp != nil {
			rbv[i] = *rbtmp
		}
		amtout[i] = *outtmp

		_, err = b.RingMatCombine(b, outtmp)
	}

	// build c_j = sum_i b_{i, j} - sum_i a_{i, j}
	c, err = NewRingMartix(amtin[0].col, 1, nttParams)
	if c == nil {
		err = errors.New("NewRingMartix fail")
		return
	}

	coeffs := make([]bigint.Int, settings.d)
	for i = 0; i < c.col; i++ {
		tmpring, _ := ring.CopyRing(&amtin[0].ringvectors[0].rings[0])
		_ = tmpring.Poly.SetCoefficients(coeffs)
		for j = 0; j < S; j++ {
			_, _ = tmpring.Add(tmpring, &amtout[j].ringvectors[i].rings[0])
		}

		for j = 0; j < M; j++ {
			_, _ = tmpring.Sub(tmpring, &amtin[j].ringvectors[i].rings[0])
		}

		c.ringvectors[i].rings[0] = *tmpring
	}

	// build d
	d, _ = NewRingMartix(c.col, 1, nttParams)
	if d == nil {
		err = errors.New("NewRingMartix fail")
		return
	}

	ring0, _ := ring.CopyRing(&c.ringvectors[0].rings[0])
	_ = ring0.Poly.SetCoefficients(coeffs)
	coeffs[0].SetInt(int64(2))
	tworing, _ := ring.CopyRing(&c.ringvectors[0].rings[0])
	_ = tworing.Poly.SetCoefficients(coeffs)
	twotmp, _ := ring.CopyRing(&c.ringvectors[0].rings[0])
	_ = twotmp.Poly.SetCoefficients(coeffs)
	seed := time.Now().UnixNano() // may consider more secure seeds
	for i = 1; i < d.col; i++ {
		tmp, _ := ring.CopyRing(&c.ringvectors[0].rings[0])
		tmpcoeffs := RqRandomB(seed, settings.d, Bd, false)
		_ = tmp.Poly.SetCoefficients(tmpcoeffs)
		d.ringvectors[i].rings[0] = *tmp

		// tmp2 = di * two
		tmp2, _ := ring.CopyRing(tmp)
		_, _ = tmp2.MulPoly(tmp, twotmp)
		// d_0 = d_0 - tmp2
		_, _ = ring0.Sub(ring0, tmp2)
		// twotmp = twotmp * 2
		_, _ = twotmp.MulPoly(twotmp, tworing)
		seed++ // seed should be reset more securely
	}

	d.ringvectors[0].rings[0] = *ring0

	// D = Com(D; rd)
	ComD, rd, err = Commitment(Ga, d, settings.B)
	// E = Com(b, t*(1-2b); rd) and F = Com(t, -t^2; rt) from BinaryCommit
	ComF, ComE, rt, rb, t, err = BinaryCommit(Gb, b, Bt, settings.B)

	Gv = make([]RingMartix, S)
	rtv = make([]RingMartix, S)

	// t_i = (t_{i, 0}, ..., t_{i, k-1})
	tisize := amtout[0].col
	ti, err := NewRingMartix(tisize, 1, nttParams)
	if ti == nil {
		err = errors.New("NewRingMartix fail")
		return
	}

	// G_i = Com(t_i; r_{t, i})
	for i = 0; i < S; i++ {
		for j = 0; j < ti.col; j++ {
			ti.ringvectors[j].rings = t.ringvectors[i*tisize+j].rings
		}

		Gtmp, rtitmp, _ := Commitment(Ga, ti, Brd)
		Gv[i] = *Gtmp
		if rtitmp != nil {
			rtv[i] = *rtitmp
		}
	}

	return
}

// Algorithm 2 prover's side after receiving x
func LinearEquationArgumentII(x *ring.Ring, b, t, c, d, rd, rb, rt *RingMartix, rav, rbv, rtv []RingMartix) (f, g, z, zg *RingMartix, zbv []RingMartix, err error) {
	// TODO: use rejection sampling to verify the bound
	var i, j uint32
	S := uint32(len(rbv))
	M := uint32(len(rav))
	nttParams := settings.nttParams

	// g = x * b + t
	g, err = NewRingMartix(b.col, 1, nttParams)
	if g == nil {
		return
	}
	for i = 0; i < b.col; i++ {
		tmpring, _ := ring.CopyRing(x)
		_, _ = tmpring.MulPoly(x, &b.ringvectors[i].rings[0])
		_, _ = tmpring.Add(tmpring, &t.ringvectors[i].rings[0])
		g.ringvectors[i].rings[0] = *tmpring
	}

	// f = x * c + d
	f, err = NewRingMartix(c.col, 1, nttParams)
	if f == nil {
		return
	}
	for i = 0; i < c.col; i++ {
		tmpring, _ := ring.CopyRing(x)
		_, _ = tmpring.MulPoly(x, &c.ringvectors[i].rings[0])
		_, _ = tmpring.Add(tmpring, &d.ringvectors[i].rings[0])
		f.ringvectors[i].rings[0] = *tmpring
	}

	// r_c = sum_i r_{b, i} - sum_i r_{a, i}
	rc, err := NewRingMartix(rbv[0].col, 1, nttParams)
	if rc == nil {
		err = errors.New("NewRingMartix fail")
		return
	}

	coeffs := make([]bigint.Int, settings.d)
	for i = 0; i < rc.col; i++ {
		tmpring, _ := ring.CopyRing(x)
		_ = tmpring.Poly.SetCoefficients(coeffs)
		for j = 0; j < S; j++ {
			_, _ = tmpring.Add(tmpring, &rbv[j].ringvectors[i].rings[0])
		}

		for j = 0; j < M; j++ {
			_, _ = tmpring.Sub(tmpring, &rav[j].ringvectors[i].rings[0])
		}

		rc.ringvectors[i].rings[0] = *tmpring
	}

	// z = x * r_c + r_d
	z, err = NewRingMartix(rc.col, 1, nttParams)
	if z == nil {
		return
	}
	for i = 0; i < rc.col; i++ {
		tmpring, _ := ring.CopyRing(x)
		_, _ = tmpring.MulPoly(x, &rc.ringvectors[i].rings[0])
		_, _ = tmpring.Add(tmpring, &rd.ringvectors[i].rings[0])
		z.ringvectors[i].rings[0] = *tmpring
	}

	// z_g = x * r_b + r_t
	zg, err = NewRingMartix(rb.col, 1, nttParams)
	if zg == nil {
		return
	}
	for i = 0; i < rb.col; i++ {
		tmpring, _ := ring.CopyRing(x)
		_, _ = tmpring.MulPoly(x, &rb.ringvectors[i].rings[0])
		_, _ = tmpring.Add(tmpring, &rt.ringvectors[i].rings[0])
		zg.ringvectors[i].rings[0] = *tmpring
	}

	// z_{b, i} = x * r_{b, i} + r_{t, i}
	zbv = make([]RingMartix, S)
	for i = 0; i < S; i++ {
		tmp, _ := NewRingMartix(rbv[i].col, 1, nttParams)
		if tmp == nil {
			return
		}
		for j = 0; j < tmp.col; j++ {
			tmpring, _ := ring.CopyRing(x)
			_, _ = tmpring.MulPoly(x, &rbv[i].ringvectors[j].rings[0])
			_, _ = tmpring.Add(tmpring, &rtv[i].ringvectors[j].rings[0])
			tmp.ringvectors[j].rings[0] = *tmpring
		}
		zbv[i] = *tmp
	}

	return
}

// Algorithm 2 verifier's side
func LinearEquationVerify(Ga, Gb, ComE, f, g, z, zg *RingMartix, x *ring.Ring, Av, Bv, zbv []RingMartix) (result bool, err error) {
	var i, j uint32
	S := uint32(len(Bv))
	M := uint32(len(Av))
	nttParams := settings.nttParams

	// sum_j 2^j * f_j =? 0
	coeffs := make([]bigint.Int, settings.d)
	coeffs[0].SetInt(2)
	two, _ := ring.CopyRing(x)
	err = two.Poly.SetCoefficients(coeffs)
	twoexp, _ := ring.CopyRing(x)
	err = twoexp.Poly.SetCoefficients(coeffs)

	sumf, _ := ring.CopyRing(x)
	err = sumf.Poly.SetCoefficients(f.ringvectors[0].rings[0].Poly.GetCoefficients())

	for i = 1; i < f.col; i++ {
		tmp, _ := ring.CopyRing(x)
		_, _ = tmp.MulPoly(&f.ringvectors[i].rings[0], twoexp)
		_, _ = sumf.Add(sumf, tmp)
		_, _ = twoexp.MulPoly(twoexp, two)
	}

	zero := bigint.NewInt(0)
	cosumf := sumf.Poly.GetCoefficients()
	for i := range cosumf {
		if !cosumf[i].EqualTo(zero) {
			return
		}
	}

	// C = sum_i B_i - sum_i A_i
	ComC, err := NewRingMartix(Av[0].col, 1, nttParams)
	if ComC == nil {
		err = errors.New("NewRingMartix fail")
		return
	}

	for i = 0; i < Av[0].col; i++ {
		tmpring, _ := ring.CopyRing(x)
		for j = 0; j < S; j++ {
			_, _ = tmpring.Add(tmpring, &Bv[j].ringvectors[i].rings[0])
		}

		for j = 0; j < M; j++ {
			_, _ = tmpring.Sub(tmpring, &Av[j].ringvectors[i].rings[0])
		}

		ComC.ringvectors[i].rings[0] = *tmpring
	}

	// D = Com(f; z) - x * C
	F, err := CommitmentWithRandom(Ga, f, z)
	xC, err := NewRingMartix(F.col, F.row, nttParams)
	if xC == nil {
		return
	}
	_ = xC.SetRingMartix(x)
	_, err = xC.RingMatScalarMul(x, ComC)
	ComD, err := xC.RingMatSub(F, xC)

	// h = g * (x - g)
	h, err := NewRingMartix(g.col, 1, nttParams)
	if h == nil {
		return
	}
	for i = 0; i < h.col; i++ {
		tmpring, _ := ring.CopyRing(x)
		_, _ = tmpring.Sub(x, &g.ringvectors[i].rings[0])
		_, _ = tmpring.MulPoly(tmpring, &g.ringvectors[i].rings[0])
		h.ringvectors[i].rings[0] = *tmpring
	}

	// F = Com(g, h; z_g) - x * E
	gh, err := NewRingMartix(g.col+h.col, 1, nttParams)
	if gh == nil {
		return
	}
	_, err = gh.RingMatCombine(g, h)
	Comgh, err := CommitmentWithRandom(Gb, gh, zg)
	xE, err := NewRingMartix(ComE.col, ComE.row, nttParams)
	if xE == nil {
		return
	}
	_ = xE.SetRingMartix(x)
	_, err = xE.RingMatScalarMul(x, ComE)
	ComF, err := xE.RingMatSub(Comgh, xE)

	// G_i = Com(g_i; z_{b, i}) - x * E
	Gv := make([]RingMartix, S)
	gi, err := NewRingMartix(settings.precision, 1, nttParams)
	if gi == nil {
		err = errors.New("NewRingMartix fail")
		return
	}

	for i = 0; i < S; i++ {
		// get f_out^(i)'s
		for j = 0; j < gi.col; j++ {
			gi.ringvectors[j].rings = g.ringvectors[i*settings.precision+j].rings
		}
		var tmp *RingMartix
		if zbv != nil {
			tmp = &zbv[i]
		}
		Comgi, _ := CommitmentWithRandom(Ga, gi, tmp)
		xB, _ := NewRingMartix(Bv[i].col, Bv[i].row, nttParams)
		if xB == nil {
			return
		}
		_ = xB.SetRingMartix(x)
		_, _ = xB.RingMatScalarMul(x, &Bv[i])
		ComG, _ := xB.RingMatSub(Comgi, xB)
		Gv[i] = *ComG
	}

	// xverify = Hash(D, E, F, Av, (B_i, G_i))
	msg := append(ComD.ToBytes(), ComE.ToBytes()...)
	msg = append(msg, ComF.ToBytes()...)
	for i = 0; i < M; i++ {
		msg = append(msg, Av[i].ToBytes()...)
	}
	for i = 0; i < S; i++ {
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

// the unbalanced linear-sum proof
// N = beta^k = len(P)
// Ga	: the n*(beta+m)-size matrix for Com(0; rho_i)
// Gb	: the n*(k*beta+m) is for BinaryCommitForDelta
func LinearSumProof(Ga, Gb, r *RingMartix, l, k, beta uint32, P []RingMartix, Bdelta, Brdelta int) (B, f, zb, zr *RingMartix, Ev []RingMartix, x *ring.Ring, err error) {
	var i, j uint32
	nttParams := settings.nttParams
	N := uint32(len(P))

	deltav := MakeDeltaMatrix(l, k, beta)
	A, B, ra, rb, a, delta, av, err := CommitForDelta(Gb, deltav, Bdelta, Brdelta, false)

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

		DebugPrint("pv"+fmt.Sprint(i), pv[i])
	}

	Ev, rhov, err := MakeEj(Ga, pv, P, beta)

	for i := range Ev {
		DebugPrint("Ev"+fmt.Sprint(i), Ev[i])
		DebugPrint("rhov"+fmt.Sprint(i), rhov[i])
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
	//E0 = &Ev[0]
	Ev = Ev[1:]
	return
}

func LinearSumVerify(Ga, Gb, ComB, f, zb, zr *RingMartix, P, Ev []RingMartix, x *ring.Ring) (result bool, err error) {
	// TODO: verify the bound
	var i, j uint32
	nttParams := settings.nttParams
	result = false
	k := uint32(len(Ev)) + 1
	beta := f.col / k
	N := uint32(len(P))

	Comf, err := CommitmentWithRandom(Gb, f, zb)

	xB, err := NewRingMartix(ComB.col, ComB.row, nttParams)
	if xB == nil {
		return
	}
	_ = xB.SetRingMartix(x)
	_, err = xB.RingMatScalarMul(x, ComB)
	ComA, err := xB.RingMatSub(Comf, xB)

	// sum_i f_{j, i} =? x
	for j = 0; j < k; j++ {
		coeffs := make([]bigint.Int, settings.d)
		tmpring, _ := ring.CopyRing(x)
		_ = tmpring.Poly.SetCoefficients(coeffs)

		for i = 0; i < beta; i++ {
			_, _ = tmpring.Add(tmpring, &f.ringvectors[j*beta+i].rings[0])
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
			_, _ = tmpring.MulPoly(tmpring, &f.ringvectors[j*beta+iv[j]].rings[0])
		}

		DebugPrint("prod_j f_{j,"+fmt.Sprint(i)+"_j}", tmpring)

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

	for i = 0; i < k-1; i++ {
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
