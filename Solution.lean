module

public import Erdos1221.ROne

/-!
# Solution

The definitions come from `Erdos1221.Defs`, a verbatim copy of those in `Challenge.lean`. The
proof is `Erdos1221.ROne.erdos_1221_r_one` in `Erdos1221/ROne.lean`.
-/

public section

open Filter
open scoped ENNReal

namespace Erdos1221

/--
De Bruijn and Erdős [dBEr49, §§2-5] proved that $\Lambda_1=\frac{1}{\log 2}$,
$\lambda_1=\frac{1}{\log 4}$, and $\mu_1=2$. A sequence which witnesses this is
$a_k=\log_2(2k-1)$. For $r=1$ the normalisation by $r$ plays no role.
-/
theorem erdos_1221.variants.r_one :
    bigLambda 1 = ENNReal.ofReal (1 / Real.log 2) ∧
      smallLambda 1 = ENNReal.ofReal (1 / Real.log 4) ∧ mu 1 = 2 :=
  ROne.erdos_1221_r_one

end Erdos1221
