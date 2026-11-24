import YM.MS.Local.Differential

set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.BV
open Function Filter Set Finset Plane Koszul Real Momentum Tensor Submodule MatrixLet
open Landau Detect
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge} {f: Grade G} {h q: ℤ}
lemma canbe {f : Grade G} (hf : f ∈ yields h q) (he:f≠0) : 0≤h ∧ q ∈ Finset.Icc (-2) 1 := by
    have hv : ∃ i,f i≠0:= not_forall.mp (fun h=> he (funext h))
    obtain ⟨⟨a,p⟩,hp⟩:=hv; have hq : ghostNo a=q:= Classical.byContradiction fun hq=> hp ((seedStar.mp hf).real' _ hq)
    have hx : 0≤ h-mslug a:= le_of_not_gt fun he=> hp (congr_fun ((seedStar.mp hf).form a |>.charge he) p)
    refine ⟨by have H:= m_pos a; omega,?_⟩; rw [← hq]; rcases a with ⟨⟨_|a,_|_⟩,u⟩ <;> norm_num [ghostNo,ghostChannel]
abbrev Baton (G : Gauge):= Grade G→ₗ[ℂ] Grade G
def pairF (h:ℤ):ℂ:= (2:ℂ)^h
def doubleT (G:Gauge): Baton G:= {
   toFun f i:= pairF (mslug i.1)* f (i.1, (2:ℝ) • i.2)
   map_add' x y:= by ext; exact mul_add ..
   map_smul' v x:= by ext; exact mul_left_comm .. }
lemma doubleF (hF:f∈yields h q) : doubleT G f= pairF h • f:= by
   ext ⟨a,p⟩; have hf := ((seedStar.mp hF).form a).scale 2 p; change (2:ℂ)^(mslug a) * f (a, (2:ℝ) • p)= (2:ℂ)^h*f (a,p); rw [hf,Complex.real_smul,Complex.ofReal_zpow,Complex.ofReal_ofNat,← mul_assoc,← zpow_add₀ (by norm_num : (2:ℂ) ≠ 0), add_sub_cancel]
lemma pair_diff (e:h≠ q) : pairF h-pairF q≠0:=sub_ne_zero.mpr (by unfold pairF; simpa only [Complex.ofReal_zpow,Complex.ofReal_ofNat] using Complex.ofReal_injective.ne ((zpow_right_strictMono₀ (show (1:ℝ)<2 by norm_num)).injective.ne e))
lemma choose_grade (G: Gauge) (h:ℤ) (s: Finset ℤ) : ∃ P : Baton G, ∀ i, (i=h ∨ i∈s) → ∀ q f, f∈ yields i q → P f= if i=h then f else 0:= by
   induction s using Finset.induction_on with
   | empty => exact ⟨LinearMap.id,fun i h q f _=> by simp_all⟩
   | insert i s hi ih=>
       obtain ⟨T,hT⟩:= ih
       rcases eq_or_ne i h with he|he; · subst i; exact ⟨T,fun x hx=> hT x (by simpa [or_assoc] using hx)⟩
       let L : Baton G := (pairF h-pairF i)⁻¹ • (doubleT G-pairF i • LinearMap.id)
       have hL x q f (hf:f∈yields x q): L f=(pairF h-pairF i)⁻¹ • (pairF x-pairF i) • f := by simp only [L, LinearMap.smul_apply,LinearMap.sub_apply, LinearMap.id_apply, doubleF hf, sub_smul]
       refine ⟨T.comp L,fun x hx q f hf=>?_⟩; rw [LinearMap.comp_apply,hL x q f hf]; by_cases h1 : x=i; · subst x; simp [he]
       rw [map_smul,map_smul,hT x (by simpa [h1] using hx) q f hf]; split <;> subst_vars <;> first | apply inv_smul_smul₀ (pair_diff (Ne.symm he)) | simp
def mask (q:ℤ) : Baton G:={
   toFun f i:= if ghostNo i.1=q then f i else 0
   map_add' a b:= by ext; split <;> simp_all -- fails
   map_smul' c v:=by ext; simp }
lemma caught (z:ℤ) (hf:f∈yields h q) : mask z f= if z=q then f else 0:= by
   ext i; by_cases hv:ghostNo i.1=q; · by_cases hz:z=q <;> simp [mask, *,eq_comm (a:=q) (b:=z)]
   simp [(seedStar.mp hf).real' i hv,mask,ite_apply]
end YM.MS.Local.BV
