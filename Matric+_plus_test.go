package main

import (
	"testing"
)

// helper functions

func setLinearEquation_plusSetting(M, S uint32) (UMC_G *RingMartix, Av, amtin, rav []RingMartix, vout []uint64) {
	setTestSettings_plus()
	outvalue := uint64(1)
	invalue := outvalue * uint64(S) / uint64(M)

	Av = make([]RingMartix, M)
	amtin = make([]RingMartix, M)
	rav = make([]RingMartix, M)

	UMC_G, _ = SamMat_plus(0)

	for i := range Av {
		Avtmp, ravtmp, amttmp, _ := Mint_plus(UMC_G, invalue)
		Av[i] = *Avtmp
		rav[i] = *ravtmp
		amtin[i] = *amttmp
	}

	vout = make([]uint64, S)
	for i := range vout {
		vout[i] = outvalue
	}

	return
}

// functional tests

func TestLinearEquationArgument_plus(t *testing.T) {
	for i := 0; i < 2; i++ {
		M := uint32(1)
		S := uint32(i + 1)

		UMC_G, Av, amtin, rav, vout := setLinearEquation_plusSetting(M, S)

		ComF, f, zg, z, Bv, zbv, x, zeta, err := LinearEquationArgument_plus(UMC_G, Av, amtin, rav, vout, 20, 10, 1, 10, 10)
		if err != nil {
			return
		}

		rst, err := LinearEquationVerify_plus(UMC_G, ComF, f, zg, z, x, zeta, Av, Bv, zbv)
		if err != nil {
			t.Errorf("Error: [TestLinearSumProof] at M=%v, S=%v. %s", M, S, err)
			return
		}

		if err != nil {
			t.Errorf("Error: [TestLinearSumProof] at M=%v, S=%v. %s", M, S, err)
			return
		}

		if !rst {
			t.Errorf("FAIL: [TestLinearSumProof] at M=%v, S=%v.", M, S)
			return
		}
	}
}

// performance tests

// M = 1; S = 1
func BenchmarkLinearEquationArgumentM1S1_plus(b *testing.B) {
	b.ResetTimer()

	M := uint32(1)
	S := uint32(1)

	UMC_G, Av, amtin, rav, vout := setLinearEquation_plusSetting(M, S)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _, _, _, _, _, _, _, _ = LinearEquationArgument_plus(UMC_G, Av, amtin, rav, vout, 20, 10, 1, 10, 10)
		}
	})
}

// M = 1; S = 1
func BenchmarkLinearEquationVerifyM1S1_plus(b *testing.B) {
	b.ResetTimer()

	M := uint32(1)
	S := uint32(1)

	UMC_G, Av, amtin, rav, vout := setLinearEquation_plusSetting(M, S)
	ComF, f, zg, z, Bv, zbv, x, zeta, _ := LinearEquationArgument_plus(UMC_G, Av, amtin, rav, vout, 20, 10, 1, 10, 10)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _ = LinearEquationVerify_plus(UMC_G, ComF, f, zg, z, x, zeta, Av, Bv, zbv)
		}
	})
}

// M = 1; S = 2
func BenchmarkLinearEquationArgumentM1S2_plus(b *testing.B) {
	b.ResetTimer()

	M := uint32(1)
	S := uint32(2)

	UMC_G, Av, amtin, rav, vout := setLinearEquation_plusSetting(M, S)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _, _, _, _, _, _, _, _ = LinearEquationArgument_plus(UMC_G, Av, amtin, rav, vout, 20, 10, 1, 10, 10)
		}
	})
}

// M = 1; S = 2
func BenchmarkLinearEquationVerifyM1S2_plus(b *testing.B) {
	b.ResetTimer()

	M := uint32(1)
	S := uint32(2)

	UMC_G, Av, amtin, rav, vout := setLinearEquation_plusSetting(M, S)
	ComF, f, zg, z, Bv, zbv, x, zeta, _ := LinearEquationArgument_plus(UMC_G, Av, amtin, rav, vout, 20, 10, 1, 10, 10)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _ = LinearEquationVerify_plus(UMC_G, ComF, f, zg, z, x, zeta, Av, Bv, zbv)
		}
	})
}
