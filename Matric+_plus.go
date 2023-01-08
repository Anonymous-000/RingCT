package main

import (
	"errors"
	"github.com/dedis/lago/bigint"
	"github.com/dedis/lago/ring"
	"time"
)

/*
The Unbalanced Linear Sum Proof is same as the Unbalanced Linear Sum Proof in MatRiC+, since MatRiCT+ does not change the ring signature part in MatRiCT+.
Therefore, we only implement the LinearEquationArgument here.
The Unbalanced Linear Sum Proof runs LinearSumProof function under the MatRiCT+ settings directly.
*/

func LinearEquationArgument_plus(UMC_G *RingMartix, Av, amtin, rav []RingMartix, vout []uint64, Bd, Br0, Br1, Brt, Brd int) (ComF, f, zg, z *RingMartix, Bv, zbv []RingMartix, x *ring.Ring, err error) {
	var i uint32
	S := uint32(len(vout))
	M := uint32(len(amtin))

	// zeta = Hash(G, Av)
	msg := append(UMC_G.ToBytes())
	for i = 0; i < M; i++ {
		msg = append(msg, Av[i].ToBytes()...)
	}
	//fmt.Printf("%v\n", md5.Sum(msg))
	zeta := make([]ring.Ring, M)
	BuildZeta(msg, zeta, &UMC_G.ringvectors[0].rings[0])
	//ShowRing(&zeta[0], settings.d)

	ComD, ComE, ComF, r0, r1, c, d, rd, Bv, Gv, rbv, rtv, err := LinearEquationArgument_plusI(zeta, UMC_G, amtin, vout, Bd, Br0, Br1, Brt, Brd)

	// x = Hash(G, Av, D, E, F, Bv, Gv)
	msg = append(msg, ComD.ToBytes()...)
	//fmt.Printf("%v\n", md5.Sum(msg))
	msg = append(msg, ComE.ToBytes()...)
	msg = append(msg, ComF.ToBytes()...)
	//fmt.Printf("%v\n", md5.Sum(msg))
	for i = 0; i < S; i++ {
		msg = append(msg, Bv[i].ToBytes()...)
		//fmt.Printf("-- Gv Prove ------\n")
		//Gv[i].ShowMatrix(settings.d)
		msg = append(msg, Gv[i].ToBytes()...)
	}
	//fmt.Printf("%v\n", md5.Sum(msg))
	x, err = ring.CopyRing(&UMC_G.ringvectors[0].rings[0])
	Hash(msg, x)

	f, zg, z, zbv, err = LinearEquationArgument_plusII(x, c, d, r0, r1, rd, rav, rbv, rtv)
	return
}

// Protocol 5 prover's side before receiving x
func LinearEquationArgument_plusI(zeta []ring.Ring, UMC_G *RingMartix, amtin []RingMartix, vout []uint64, Bd, Br0, Br1, Brt, Brd int) (ComD, ComE, ComF, r0, r1, c, d, rd *RingMartix, Bv, Gv, rbv, rtv []RingMartix, err error) {
	var i, j uint32
	nttParams := settings.nttParams
	S := uint32(len(vout))
	M := uint32(len(amtin))

	// mint coins for outputs
	Bv = make([]RingMartix, S)
	Gv = make([]RingMartix, S)
	rbv = make([]RingMartix, S)
	rtv = make([]RingMartix, S)
	amtout := make([]RingMartix, S)

	for i = 0; i < S; i++ {
		Btmp, rbtmp, outtmp, _ := Mint_plus(UMC_G, vout[i])
		Bv[i] = *Btmp
		if rbtmp != nil {
			rbv[i] = *rbtmp
		}
		amtout[i] = *outtmp
	}

	// build c_j = sum_i b_{i, j} - sum_i a_{i, j}
	c, err = NewRingMartix(1, 1, nttParams)
	if c == nil {
		err = errors.New("NewRingMartix fail")
		return
	}

	coeffs := make([]bigint.Int, settings.d)
	tmpring, _ := ring.CopyRing(&amtin[0].ringvectors[0].rings[0])
	_ = tmpring.Poly.SetCoefficients(coeffs)
	for i = 0; i < S; i++ {
		_, _ = tmpring.Add(tmpring, &amtout[i].ringvectors[0].rings[0])
	}
	for i = 0; i < M; i++ {
		_, _ = tmpring.Sub(tmpring, &amtin[i].ringvectors[0].rings[0])
	}
	c.ringvectors[0].rings[0] = *tmpring

	// build d. d[i] = d'[i] - 2 * d'[i+1]
	d, _ = NewRingMartix(1, 1, nttParams)
	if d == nil {
		err = errors.New("NewRingMartix fail")
		return
	}

	delta := settings.d / settings.precision
	seed := time.Now().UnixNano()
	d_p := RqRandomB(seed, settings.d, Bd, false)
	for i = 0; i < settings.precision; i++ {
		for j = 0; j < delta; j++ {
			if i == 0 {
				// d_0 = 0 - 2 * d'_{j + 1}
				coeffs[delta*i+j].Lsh(&d_p[delta*(i+1)+j], 1)
				coeffs[delta*i+j].Neg(&coeffs[delta*i+j], &settings.q)
			} else if i == settings.precision-1 {
				// d_{j - 1} = d'_{j - 1} - 0
				coeffs[delta*i+j].SetBigInt(&d_p[delta*i+j])
			} else {
				// d_j = d'_j - 2 * d'_{j + 1}
				coeffs[delta*i+j].Lsh(&d_p[delta*(i+1)+j], 1)
				coeffs[delta*i+j].Sub(&d_p[delta*i+j], &coeffs[delta*i+j])
			}
			coeffs[delta*i+j].Mod(&coeffs[delta*i+j], &settings.q)
		}
	}

	dring, _ := ring.CopyRing(&c.ringvectors[0].rings[0])
	_ = dring.Poly.SetCoefficients(coeffs)
	d.ringvectors[0].rings[0] = *dring

	//d.ShowMatrix(settings.d)
	// D = Com(D; rd)
	ComD, rd, err = UMCCom(UMC_G, d, Brd)

	//fmt.Printf("-- D Prove ------\n")
	//ComD.ShowMatrix(settings.d)

	// compute g_hat_0 and g_hat_1
	// gm is the last row of UMC_G (1 * m).
	// gzero is G0 all except the last row of UMC_G ((n - 1) * m)
	gm, _ := NewRingMartix(1, UMC_G.row, nttParams)
	if gm == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	gm.CopyLastRowMartix(UMC_G)
	gzero, _ := NewRingMartix(UMC_G.col-1, UMC_G.row, nttParams)
	if gm == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	gzero.CopyAllButLastRowMartix(UMC_G)

	a0, _ := NewRingMartix(1, 1, nttParams)
	if a0 == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	a0.SetRingMartix(&UMC_G.ringvectors[0].rings[0])
	a1, _ := NewRingMartix(1, 1, nttParams)
	if a1 == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	a1.SetRingMartix(&UMC_G.ringvectors[0].rings[0])

	g0, _ := NewRingMartix(1, 1, nttParams)
	if g0 == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	g0.SetZeroRingMartix(&UMC_G.ringvectors[0].rings[0], settings.d)

	g1, _ := NewRingMartix(1, 1, nttParams)
	if g1 == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	g1.SetZeroRingMartix(&UMC_G.ringvectors[0].rings[0], settings.d)

	for i = 0; i < S; i++ {
		seed++
		r, _ := NewRingMartix(UMC_G.row, 1, nttParams)
		r.SetRandomBRingMartix(&UMC_G.ringvectors[0].rings[0], seed, settings.d, Brt, false)
		rtv[i] = *r

		// G_i = G0 * rt_i
		gi, _ := NewRingMartix(UMC_G.col-1, UMC_G.row, nttParams)
		gi.SetRingMartix(&UMC_G.ringvectors[0].rings[0])
		_, err = gi.RingMatMul(gzero, r)
		Gv[i] = *gi
		//fmt.Printf("-- Gi Prove ------\n")
		//Gv[i].ShowMatrix(settings.d)

		// g0 = sum <gm, rt_i> zeta_i
		// g1 = sum zeta_i <gm, rt_i> (1 - 2 * b_i)
		// TODO: should use Hadamard product to compute
		_, err = a0.RingMatMul(gm, r)         // a = <gm, rt_i>
		two := make([]bigint.Int, settings.d) // 2
		two[0].SetInt(int64(2))
		tworing, _ := ring.CopyRing(&c.ringvectors[0].rings[0])
		_ = tworing.Poly.SetCoefficients(two)

		_, err = a1.RingMatScalarMul(tworing, &amtout[i]) // 2 * b_i
		_, err = a1.RingMatMul(a0, a1)                    // 2 * a * b_i

		_, err = a1.RingMatSub(a0, a1)             // a - 2 * a * b_i
		_, err = a1.RingMatScalarMul(&zeta[i], a1) // zeta_i (a - 2 * a * b_i)
		_, err = g1.RingMatAdd(g1, a1)

		_, err = a0.RingMatMul(a0, a0)             // a^2
		_, err = a0.RingMatScalarMul(&zeta[i], a0) // zeta_i a^2
		_, err = g0.RingMatAdd(g0, a0)
	}

	// E = Com(g0; r0)
	ComE, r0, _ = UMCCom(UMC_G, g0, Br0)

	//fmt.Printf("-- E Prove ------\n")
	//ComE.ShowMatrix(settings.d)

	// F = Com(g1; r1)
	ComF, r1, _ = UMCCom(UMC_G, g1, Br1)

	//fmt.Printf("-- F Prove ------\n")
	//ComF.ShowMatrix(settings.d)

	return
}

// Algorithm 2 prover's side after receiving x
func LinearEquationArgument_plusII(x *ring.Ring, c, d, r0, r1, rd *RingMartix, rav, rbv, rtv []RingMartix) (f, zg, z *RingMartix, zbv []RingMartix, err error) {
	// TODO: use rejection sampling to verify the bound
	var i, j uint32
	S := uint32(len(rbv))
	M := uint32(len(rav))
	nttParams := settings.nttParams

	// zg = x * r1 + r0
	zg, err = NewRingMartix(r0.col, 1, nttParams)
	if zg == nil {
		return
	}
	for i = 0; i < zg.col; i++ {
		tmpring, _ := ring.CopyRing(x)
		_, _ = tmpring.MulPoly(x, &r1.ringvectors[i].rings[0])
		_, _ = tmpring.Add(tmpring, &r0.ringvectors[i].rings[0])
		zg.ringvectors[i].rings[0] = *tmpring
	}

	// zb_i = x * rb_i + rt_i
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

	// z = sum_i r_{b, i} - sum_i r_{a, i} + rd
	z, err = NewRingMartix(rbv[0].col, 1, nttParams)
	if z == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	coeffs := make([]bigint.Int, settings.d)
	for i = 0; i < z.col; i++ {
		tmpring, _ := ring.CopyRing(x)
		_ = tmpring.Poly.SetCoefficients(coeffs)
		for j = 0; j < S; j++ {
			_, _ = tmpring.Add(tmpring, &rbv[j].ringvectors[i].rings[0])
		}

		for j = 0; j < M; j++ {
			_, _ = tmpring.Sub(tmpring, &rav[j].ringvectors[i].rings[0])
		}

		_, _ = tmpring.Add(tmpring, &rd.ringvectors[i].rings[0])

		z.ringvectors[i].rings[0] = *tmpring
	}

	// f = x * c + d
	f, err = NewRingMartix(1, 1, nttParams)
	if f == nil {
		return
	}
	tmpring, _ := ring.CopyRing(x)
	_, _ = tmpring.MulPoly(x, &c.ringvectors[0].rings[0])
	_, _ = tmpring.Add(tmpring, &d.ringvectors[0].rings[0])
	f.ringvectors[0].rings[0] = *tmpring

	return
}

// Algorithm 2 verifier's side
func LinearEquationVerify_plus(UMC_G, ComF, f, zg, z *RingMartix, x *ring.Ring, Av, Bv, zbv []RingMartix) (result bool, err error) {
	var i uint32
	S := uint32(len(Bv))
	M := uint32(len(Av))
	nttParams := settings.nttParams

	result = false

	// sum_j 2^j * f_j =? 0
	if !CheckPackedf(f) {
		return
	}

	msg := append(UMC_G.ToBytes())
	for i = 0; i < M; i++ {
		msg = append(msg, Av[i].ToBytes()...)
	}
	//fmt.Printf("%v\n", md5.Sum(msg))
	zeta := make([]ring.Ring, M)
	BuildZeta(msg, zeta, &UMC_G.ringvectors[0].rings[0])
	//ShowRing(&zeta[0], settings.d)

	// C = sum B_i - sum A_i
	ComC, err := NewRingMartix(UMC_G.col, 1, nttParams)
	if ComC == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	ComC.SetRingMartix(&zeta[0])
	for i = 0; i < S; i++ {
		_, _ = ComC.RingMatAdd(ComC, &Bv[i])
	}
	for i = 0; i < M; i++ {
		_, _ = ComC.RingMatSub(ComC, &Av[i])
	}

	// D = UMC(f; z) - x * C
	UF, err := UMCComWithRandom(UMC_G, f, z)
	xC, err := NewRingMartix(UF.col, UF.row, nttParams)
	if xC == nil {
		return
	}
	_ = xC.SetRingMartix(x)
	_, err = xC.RingMatScalarMul(x, ComC)
	ComD, err := xC.RingMatSub(UF, xC)

	//fmt.Printf("-- D Verify ------\n")
	//ComD.ShowMatrix(settings.d)

	// Compute h = sum zeta_i h_i
	gm, _ := NewRingMartix(1, UMC_G.row, nttParams)
	if gm == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	gm.CopyLastRowMartix(UMC_G)
	gzero, _ := NewRingMartix(UMC_G.col-1, UMC_G.row, nttParams)
	if gm == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	gzero.CopyAllButLastRowMartix(UMC_G)

	h, _ := NewRingMartix(1, 1, nttParams)
	if h == nil {
		err = errors.New("NewRingMartix fail")
		return
	}
	h.SetZeroRingMartix(&UMC_G.ringvectors[0].rings[0], settings.d)

	Gv := make([]RingMartix, S)

	for i = 0; i < S; i++ {
		// Bi = (ui, umi)
		xumi, _ := NewRingMartix(1, 1, nttParams)
		if xumi == nil {
			err = errors.New("NewRingMartix fail")
			return
		}
		xumi.SetRingMartix(x)
		umi, _ := NewRingMartix(1, 1, nttParams)
		if umi == nil {
			err = errors.New("NewRingMartix fail")
			return
		}
		umi.CopyLastRowMartix(&Bv[i])
		_, err = xumi.RingMatScalarMul(x, umi)

		// h_i = <gm, zb_i> - x * um_i
		hi, _ := NewRingMartix(1, 1, nttParams)
		if hi == nil {
			err = errors.New("NewRingMartix fail")
			return
		}
		hi.SetRingMartix(x)
		_, _ = hi.RingMatMul(gm, &zbv[i])
		_, _ = hi.RingMatSub(hi, xumi)

		// h_i * (h_i + x)
		// TODO: should use Hadamard product to compute
		_, _ = xumi.RingMatScalarAdd(x, hi)
		_, _ = hi.RingMatMul(hi, xumi)

		_, _ = hi.RingMatScalarMul(&zeta[i], hi)
		_, _ = h.RingMatAdd(h, hi)

		// G_i = G0 * zb_i - x * u_i
		xui, _ := NewRingMartix(Bv[i].col-1, 1, nttParams)
		if xui == nil {
			err = errors.New("NewRingMartix fail")
			return
		}
		xui.SetRingMartix(x)
		ui, _ := NewRingMartix(Bv[i].col-1, 1, nttParams)
		if ui == nil {
			err = errors.New("NewRingMartix fail")
			return
		}
		ui.CopyAllButLastRowMartix(&Bv[i])
		_, err = xui.RingMatScalarMul(x, ui)

		gi, _ := NewRingMartix(Bv[i].col-1, 1, nttParams)
		if gi == nil {
			err = errors.New("NewRingMartix fail")
			return
		}
		gi.SetRingMartix(x)
		_, _ = gi.RingMatMul(gzero, &zbv[i])
		_, _ = gi.RingMatSub(gi, xui)
		Gv[i] = *gi
		//fmt.Printf("-- Gi Verify ------\n")
		//Gv[i].ShowMatrix(settings.d)
	}

	// E = UMC(h, zg) - x * F
	Uh, err := UMCComWithRandom(UMC_G, h, zg)
	xF, err := NewRingMartix(Uh.col, Uh.row, nttParams)
	if xF == nil {
		return
	}
	_ = xF.SetRingMartix(x)
	_, err = xF.RingMatScalarMul(x, ComF)
	ComE, err := xF.RingMatSub(Uh, xF)

	//fmt.Printf("-- E Verify ------\n")
	//ComE.ShowMatrix(settings.d)

	// xverify = Hash(G, Av, D, E, F, Bv, Gv)
	msg = append(msg, ComD.ToBytes()...)
	//fmt.Printf("%v\n", md5.Sum(msg))
	msg = append(msg, ComE.ToBytes()...)
	msg = append(msg, ComF.ToBytes()...)
	//fmt.Printf("%v\n", md5.Sum(msg))
	for i = 0; i < S; i++ {
		msg = append(msg, Bv[i].ToBytes()...)
		//fmt.Printf("-- Gi Verify ------\n")
		//Gv[i].ShowMatrix(settings.d)
		msg = append(msg, Gv[i].ToBytes()...)
	}
	//fmt.Printf("%v\n", md5.Sum(msg))
	xverify, err := ring.CopyRing(x)
	Hash(msg, xverify)

	//ShowRing(xverify, settings.d)

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
