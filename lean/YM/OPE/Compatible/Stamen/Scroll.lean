import YM.OPE.Compatible.Stamen.Dusk
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
def sheetM (a:Root (Shade H))(v:fieldX (Shade H))(t:ℝ):= board (lotU (t • v)) a
abbrev moor (a:Root (Shade H)):Page (Shade H) 1:= fun _=>a
lemma moorEq (v:fieldX (Shade H))(a:Root (Shade H))(t:ℝ):sheetM a v t=verseX (ships (moor a)) (lotU (t • v)):=by rw [← issue,wordX,Fin.prod_univ_one];rfl
lemma smoothZ (v:fieldX (Shade H))(a:Root (Shade H)):ContDiff ℝ ⊤ (sheetM a v):=by rw [funext (moorEq v a)]; exact cash_smooth ..
lemma chargeP (v:fieldX (Shade H)) (a:Root (Shade H)): sheetM a v 0=0:=by unfold sheetM board; rw [taPZ,Gauge.curvature_unit];rfl
abbrev mores (v:fieldX (Shade H))(j:ℕ):fieldX (Shade H):=fun a=> WardBin.leading j (sheetM a v)
lemma moreH (v:fieldX (Shade H)) (a:Root (Shade H)): mores v 1 a=risingO v a:=by rw [mores,WardBin.leading,iteratedDeriv_one]; rw[show deriv _ _= _ from (show HasDerivAt (sheetM a v) (risingO v a) _ from arcRead ..).deriv]; simp
lemma plumQ (p:fieldX (Shade H))(hp:Quiet p 0)(n:ℕ): Quiet (mores p n) n:=by
      obtain ⟨v,hv,Hv⟩:= staffQ _ hp; obtain ⟨C,hc,Ht⟩:= ozone H 1 v (heraldD H) hv (lumenD _) n; let X:ℝ:= ((n.factorial:ℝ)⁻¹*C)* (3:ℝ)^n; refine ⟨X,by unfold X; positivity,fun i=>?_⟩; let u:=moor i; unfold mores WardBin.leading; rw [norm_smul,Real.norm_of_nonneg (by positivity), funext (moorEq p i)]; apply (mul_le_mul_of_nonneg_left (Ht _ _ (theater u) (fun j _=>Hv j) 0) (by positivity)).trans
      let z:ℝ:= notch i.1; have hs: lawn (ships u) + 1≤3*notch i.1:=by
             unfold lawn; rw [Fin.sum_univ_one]; change (ringO (i.1,i.2.1)).length+_≤_; unfold notch; have he:=lengthK (i.1,i.2.1); dsimp only at he;omega
      rw[show X*poise n i.1=((n.factorial:ℝ)⁻¹)*(C*(3*z)^n) from by unfold X poise; rw [mul_pow]; ring]; apply mul_le_mul_of_nonneg_left _ (by positivity); apply mul_le_mul_of_nonneg_left _ hc; apply pow_le_pow_left₀ (by positivity); unfold z; exact_mod_cast hs
end YM.OPE.Silt.Phere
