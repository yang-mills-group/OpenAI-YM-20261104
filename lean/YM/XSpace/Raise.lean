import YM.XSpace.Magnify

/-!
# Core compensation row β-local (complex; not yet signed-symmetrized)

Witness family raw correction through each horizon. Later gorge geometry determines χ,
then leading identities at the regulator show separated report convergence after kpos.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Furlough
open Function Set Filter Lows Scale Mu Uptown Bracket Normalize Maxwell Maxwell.Free MvPolynomial Next.Rank.Normal Contraction Finsupp Lattice Future
open scoped Topology BigOperators ContDiff
variable {G:Gauge} {d:ℕ} (W:Initialize G)(c:Shade.Cut)

def Lm (d:ℕ): (On.Grade G d) →ₗ[ℂ] (Labels.Label G d):= On.sectionMap d ∘ₗ Submodule.inclusion (show On.Grade G d≤shellSector G d from inf_le_left)
lemma Lm_ap (p:On.Grade G d): Lm d p=Price.preparedL p:=rfl
def screen1 (d:ℕ)(a:ℝ): (On.Grade G d) →ₗ[ℂ] Stamp G where
  toFun p:= Prelude.fuse (W.surveys d) p c a
  map_add' p q:= by
    simp only [Prelude.fuse,Prelude.mark1,Prelude.enter0,Prelude.startField,Chart2.p1,← Lm_ap, map_add,Submodule.coe_add,LinearMap.add_apply]; abel
  map_smul' t p :=by simp only [Prelude.fuse,Prelude.mark1,Prelude.enter0,Prelude.startField,Chart2.p1,← Lm_ap, map_smul, PowerSeries.coeff_smul,Submodule.coe_smul,LinearMap.smul_apply,RingHom.id_apply, smul_sub]

def caseView (d:ℕ)(a:ℝ): (On.Grade G d)→ₗ[ℂ] Sec G d:= LinearMap.codRestrict _ ((archive d).toLinearMap ∘ₗ trunc coin d ∘ₗ (overture d).toLinearMap ∘ₗ screen1 W c d a) (fun p=> preserve _ (Show.plan (W.surveys d) c _ p) d d)
def repair (d:ℕ)(a:ℝ): (On.Grade G d) →ₗ[ℂ] Sec G d:= (migrate W d).symm.toLinearMap ∘ₗ caseView W c d a
def rf (d:ℕ)(a:ℝ): (On.Grade G d) →ₗ[ℂ] Stamp G:= screenplay W d ∘ₗ repair W c d a
def compensate (d:ℕ)(a:ℝ): (On.Grade G d) →ₗ[ℂ] Stamp G:= screen1 W c d a-rf W c d a
lemma cap_raw (p:On.Grade G d)(a:ℝ):
    trunc coin d (overture d (compensate W c d a p)) = (divide (bevel (W.surveys d) p c a)).val:=by
  change trunc coin d (overture d (screen1 W c d a p-rf W c d a p))=_; rw [map_sub,map_sub]; let A:=screen1 W c d a p; change _-_=_-cross _ _; congr 1
  apply sameCap; intro B
  have hx: archive d (trunc coin d (overture d (rf W c d a p)))=archive d (trunc coin d (overture d A)):= congr_arg Subtype.val ((migrate W d).apply_symm_apply (caseView W c d a p)); rw [← dictoB]; rw [show bevel (W.surveys d) p c a = overture d A from rfl,← hx];
  rw [dictoB,radial_keeps,show cross (radial G d) (overture _ (rf W c d a p))= _ from radialPoly W _]; rfl

-- unit strictly no correction
lemma leaves (a:ℝ) (p:On.Grade G 0)(h:p.val=1): caseView W c 0 a p=0:=by
  apply Subtype.ext; set S:=W.surveys 0; change archive 0 (trunc coin 0 (bevel S p c a))=0; unfold bevel; rw [← cutback];
  suffices archive 0 (overture 0 (Prelude.fuse S p c a))=0 by rw [this,map_zero]
  apply Maxwell.equalPol; intro A; rw [map_zero,dicto,music_at]
  have he:seat 0 A=0:=funext fun i=> by rw [show i=0 by exact Fin.eq_zero i]; rfl
  have hh: Price.preparedL p=Labels.unit G 0:=Subtype.ext (by rw [Price.preparedV,h,map_one];rfl)
  rw [he,map_zero,Prelude.fuse,Prelude.mark1,Prelude.startField,hh,S.wick_unit,Prelude.enter0,hh, Chart2.p1]; change Chart2.pit (0:Trace.Contact G) ( flicker (PowerSeries.coeff 1 (Chart2.toy S (0:Cover) 1))-tie G (Encore.reel S 0 1) _)=_
  rw [map_one (Chart2.toy S (0:Cover)),show PowerSeries.coeff 1 (1:PowerSeries (Stamp G)) =0 by simp,map_zero,map_one,one_tie,zero_sub,map_neg]; unfold Prelude.engine; simp only [_root_.map_sum,show ∀ (f:Cover→Stamp G)(p:Prelude.Mark),Chart2.pit (G:=G) 0 (Prelude.send p f) = Prelude.send p (fun i=> Chart2.pit (G:=G) 0 (f i)) from fun f p=> Prelude.by_send (Chart2.pit (G:=G) 0).toLinearMap p f,Chart2.price_at, Chart2.diagnostic,map_zero,inner_zero_left, Complex.ofReal_zero]; simp [Prelude.send]
lemma strictly (a:ℝ) (p:On.Grade G 0)(h:p.val=1): repair W c 0 a p=0:=by rw [repair,LinearMap.comp_apply,leaves W c a p h,map_zero]

lemma shore (p:On.Grade G d)(a:ℝ): (portal W d (repair W c d a p)).val=archive d (debit (W.surveys d) p c a).val:= congr_arg Subtype.val ((migrate W d).apply_symm_apply _)
variable {ι:Type}{L:Filter ι} [L.IsCountablyGenerated]{a:ι→ℝ}(S:Tendsto a L (𝓝 0))(he:∀ᶠ i in L,0<a i)
include he S in
theorem greeting (p:On.Grade G d): By ℂ L (fun i=> (a i:ℂ) • repair W c d (a i) p) 0:=by
  let f (x: TaylorTower G):Module.Dual ℂ (Sec G d):= (Maxwell.probe x).toLinearMap ∘ₗ (shellSector G d).subtype ∘ₗ portal W d
  refine redeemBy f ?_ ?_; intro x hx; apply (exchangeable W d).1; rw [map_zero]; apply Subtype.ext; apply Maxwell.equalPol; intro t; change probe t (_) = probe t 0; rw [map_zero]; exact hx t
  intro x; simp_rw [map_zero,map_smul]; change Tendsto (fun i=> (a i:ℂ) * Maxwell.probe x (portal W d _).val) L _; simp_rw [shore];
  have hh:= fee_hint (W.surveys d) p c S he ((probe x).toLinearMap ∘ₗ (archive d).toLinearMap ∘ₗ (Load G d d).subtype); simp_rw [map_smul,map_zero] at hh; exact hh
include he S in
theorem wires (p:On.Grade G d){B:ι→ Hat G d}(h:Likely L B): Likely L (fun i=> Drama.tick a i d* Drama.LTop (compensate W c d (a i) p) (a i) (B i)):=by
  have hP:= Drama.atmosphere h (compensatory (W.surveys d) p c S he); apply hP.congr; filter_upwards with i; unfold Drama.LTop; rw [Submodule.coe_smul, map_smul, cap_raw,stageLift, scaled]; rfl
end YM.XSpace.Furlough
