# RingCT_Implementation

## Description

This is a _**toy**_ implementation of [**MatRiCT**](https://eprint.iacr.org/2019/1287.pdf) and our work (**Matric+**). Please do **NOT** use this in production environment.

The balance proof and one-out-of-many proof are implemented separately to compare the performance in more details.

## Package Required
- The ring operations are provided from [**LAGO**](https://github.com/dedis/lago). Please run `git get github.com/dedis/lago` before testing.

## Remarks
- As the algorithm 9 and 10 in MatRiCT only support _**less than two outputs and one input**_ (embedding corrector values in binary proofs), `BalanceProof` function returns directly when dealing with more inputs/outputs. The balance proof verification, `BalanceVerify`, will fail when removing the check of `S` amd `M` in `BalanceProof`, unless corrector values happen to be binaries.
- There is a **BUG** in the [`MulPoly`](https://github.com/dedis/lago/blob/789763ed5fb5e3420cc72260ab8d005f8c06ea3f/polynomial/polynomial.go#L143L159) function of [**LAGO**](https://github.com/dedis/lago). Specifically, when dealing with same inputs, `p.MulPoly(p1, p1)`, `p1` will run _**two times of NTT instead of one**_. Thus, `MulPolyBug` is used in this package to indicate whether this bug is fixed or not. This package will work when directly setting this value to `true` without fixing. Alternatively, fixing the bug as follows will make this package more efficient:
```go
func (p *Poly) MulPoly(p1, p2 *Poly) (*Poly, error) {
    if p.n != p1.n || !p.q.EqualTo(&p1.q) {
        return nil, errors.New("unmatched degree or module")
    }
    p1.NTT()
    if p1 != p2 {
        p2.NTT()
    }
    p.MulCoeffs(p1, p2)
    p.Mod(p, p.q)
    p.InverseNTT()
    if p != p1 {
        p1.InverseNTT()
    }
    if p != p2 && p1 != p2 {
        p2.InverseNTT()
    }
    return p, nil
}
```
