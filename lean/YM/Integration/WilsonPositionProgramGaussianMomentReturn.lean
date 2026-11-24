import YM.Integration.WilsonPositionProgramGaussianMomentBank

/-! Integrate the complete weighted proper and full ordinary faces in their original finite Gaussian. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramGaussianMomentReturn
open Finset MeasureTheory Multi Marker Next.SectorChange Next.Rank Comparison.RG02.Cumulants
open WilsonPositionProgramGaussianMomentBank WilsonMarkedInheritedGaussianMoment
open scoped BigOperators Classical
variable {V I:Type}[DecidableEq V][DecidableEq I][Fintype I]{R:Census V}
  (Q:Matrix I I ℝ)(positive:Q.PosDef)(hQ:Q.IsSymm)(σ:ℝ)(diag:∀i,Q i i≤σ)

def room (R:Census V)(I:Type)[Fintype I](σ B:ℝ)(k:ℕ):ℝ:=
  words R*B^(number R)*charge I σ (k*number R)

def difference (R:Census V)(I:Type)[Fintype I](σ B:ℝ)(k:ℕ):ℝ:=
  words R*(number R:ℝ)*B^(number R)*charge I σ (k*(number R+1))

include positive diag in
private theorem paid (F:Normal.poly I)(t c:ℝ)(ht:0<t)(hc:0≤c)(k:ℕ)
    (test:∀z:I→ℝ,t*‖Cloud.paint z F‖≤c*(1+‖z‖)^k):
    t*‖Cloud.wick Q hQ (Cloud.shift (0:I→ℝ)) F‖ ≤ c*charge I σ k := by
  have scalar(v:ℂ):‖(t:ℂ)*v‖=t*‖v‖:=by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
  have changed(z:I→ℝ):‖Cloud.paint z ((t:ℂ) • F)‖≤c*(1+‖z‖)^k:=by
    simpa only [map_smul,smul_eq_mul,scalar] using test z
  have ticket:=WilsonPositionProgramGaussianProductPrice.measured Q positive hQ σ diag ((t:ℂ) • F) k hc changed
  simpa only [map_smul,smul_eq_mul,scalar] using ticket

omit [Fintype I] [DecidableEq I] in
private theorem read (Q:Matrix I I ℝ)(hQ:Q.IsSymm)(p:Hot R→Normal.poly I)(s:R.Mode):
    (Cloud.prescription Q hQ (Cloud.shift (0:I→ℝ)) p).part s=
      Cloud.wick Q hQ (Cloud.shift (0:I→ℝ)) (Cloud.integrand p s):=rfl

include positive diag in
private theorem ordinary (w:V→ℝ)(hw:∀v,0<w v)(p:Hot R→Normal.poly I)(s:R.Mode)(B:ℝ)(hb:0≤B)(k:ℕ)
    (test:∀z:I→ℝ,Poly.toll w s*‖Cloud.paint z (Cloud.integrand p s)‖ ≤
      (words R*B^(number R))*(1+‖z‖)^(k*number R)):
    Poly.toll w s*‖(Cloud.prescription Q hQ (Cloud.shift (0:I→ℝ)) p).part s‖≤room R I σ B k:=by
  rw [read]
  have pos:0≤ words R:=by unfold words WilsonPositionProgramDisjointWallet.stock WilsonPositionProgramDisjointWallet.salary;positivity
  exact paid Q positive hQ σ diag _ _ _ (Poly.worth hw s) (mul_nonneg pos (pow_nonneg hb _)) _ test

include positive diag in
private theorem mixed (w:V→ℝ)(hw:∀v,0<w v)(p q:Hot R→Normal.poly I)(s:R.Mode)(B δ:ℝ)(hb:0≤B)(hd:0≤δ)(k:ℕ)
    (test:∀z:I→ℝ,Poly.toll w s*‖Cloud.paint z (Cloud.integrand p s-Cloud.integrand q s)‖ ≤
      (δ*(words R*(number R:ℝ)*B^(number R)))*(1+‖z‖)^(k*(number R+1))):
    Poly.toll w s*‖(Cloud.prescription Q hQ (Cloud.shift (0:I→ℝ)) p).part s-
      (Cloud.prescription Q hQ (Cloud.shift (0:I→ℝ)) q).part s‖≤δ*difference R I σ B k:=by
  rw [read,read]
  have hword:0≤ words R:=by unfold words WilsonPositionProgramDisjointWallet.stock WilsonPositionProgramDisjointWallet.salary;positivity
  let c:=words R*(number R:ℝ)*B^(number R)
  have hc:0≤c:=by dsimp [c];positivity
  have paid₁:=paid Q positive hQ σ diag (Cloud.integrand p s-Cloud.integrand q s) (Poly.toll w s)
    (δ*c) (Poly.worth hw s) (mul_nonneg hd hc) (k*(number R+1)) test
  rw [map_sub] at paid₁
  exact paid₁.trans_eq (mul_assoc δ c (charge I σ (k*(number R+1))))

include positive diag in
theorem original (w:V→ℝ)(hw:∀v,0<w v)(p q:Hot R→Normal.poly I)(k:ℕ){B δ:ℝ}(hb:1≤B)(hd:0≤δ)
    (hp:∀i z,Poly.toll w i.val*‖Cloud.paint z (p i)‖≤B*(1+‖z‖)^k)
    (hq:∀i z,Poly.toll w i.val*‖Cloud.paint z (q i)‖≤B*(1+‖z‖)^k)
    (fee:∀i z,Poly.toll w i.val*‖Cloud.paint z (p i-q i)‖≤δ*(1+‖z‖)^k)(s:R.Mode):
    let left:=Cloud.prescription Q hQ (Cloud.shift (0:I→ℝ)) p
    let right:=Cloud.prescription Q hQ (Cloud.shift (0:I→ℝ)) q
    Poly.toll w s*‖left.part s‖ ≤ room R I σ B k ∧
    Poly.toll w s*‖left.part s-right.part s‖ ≤ δ*difference R I σ B k := by
  exact ⟨ordinary Q positive hQ σ diag w hw p s B (zero_le_one.trans hb) k
      (fun z=>(pointwise w hw p q k hb hd hp hq fee s z).1),
    mixed Q positive hQ σ diag w hw p q s B δ (zero_le_one.trans hb) hd k
      (fun z=>(pointwise w hw p q k hb hd hp hq fee s z).2)⟩

end YM.Integration.WilsonPositionProgramGaussianMomentReturn
end
