import YM.OPE.Compatible.Roost.Mood
/-!
# count transition switch φ orientation - prove launch guidance. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b u:ℝ}{A:Alps K T i v}{D:Alps K T j v'} {U:Boxes G P' K.K}
local notation "Y!"=>solar G d τ
local notation "T!"=> Tracts G d τ
open JetS
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}
variable (H hs) (h:Aware d τ)
section
variable (L:Flight i j) (V:Medal L.patch G K.K i)(hi:Mag i j)(hp:A.gear=L.wing)(hz:D.gear=L.land)
local notation "Ψ"=>boxF L K hi V A.gear
variable (t:Town A D (boxF L K hi V A.gear) R u)
include t hp hz H hs
lemma frontierY (x:Tracts G d τ)(i':Phase)(h':rare i' x) :
    let T:=MotionX H hs t h hi.1 hi.2.1
    rare i' (T x)∧ T x i'=journey L K.K hi.2.1 (K.affordable _) (x i'):=by
         intro W; let F:= Fallix G h K A.gear hi.1; let E:=Fallix G h K D.gear hi.2.1; let p:=F x; let v:= W x; let z:=yankV D t H hs h p; have hv: E v=z:= E.apply_symm_apply _; obtain ⟨hS,Ht⟩:=starMark h x A.gear hi.1 i' h' (K:=K); have hz'(s:Phase)(ht:s < i'): z.val s=0:= (lipY H hs t h i' p hS).2 s ht.le|>.trans ((lipY H hs t h i' p hS).1 s ht)
         have hT: rare i' v:= receiving h v _ hi.2.1 _ (show ∀ j < i', (E v).val j=0 from hv.symm ▸ hz') (K:=K); refine ⟨hT,?_⟩
         let B:= boostS (atlasF G D.gear hi.2.1 K.K) (-(1/2:ℝ)) (τ i') (d+i'.val); apply Subtype.ext; apply (show Injective B from (show LeftInverse (boostS (atlasF G D.gear hi.2.1 K.K) (1/2:ℝ) (τ i') (d+i'.val)) B from fun x=> sustain ..).injective)
         rw [show B ((W x i').val)= z.val i' from (starMark h _ D.gear hi.2.1 _ hT (K:=K)).2.symm.trans (hv ▸ rfl)]; let R':RollD A Ψ R:=⟨hs,H,t.eph⟩; let T:=actor A Ψ R 0 R' h; rw [show z.val i'=T p.val i' from (lipY H hs t h i' p hS).2 i' le_rfl]; unfold T; rw [actorA, Finset.sum_eq_single i']; rotate_left
         · intro j _ hj; rcases lt_or_gt_of_ne hj with hv|hv; rw [show p.val j=0 from hS _ hv,map_zero]; rw [acceptZ 0 _ _ _ R' h i' j hv];rfl
         · simp
         unfold Drift.chamber; rw [dif_pos (le_refl _),reacquire]; let S:=sectorOp L.patch K.K A Ψ R 0 (awareLeaf h i') d i' i' hs t.eph H; change S (p.val i')= _; have hY:= invest L A D V R hi hp hz hs 0 H i' d; have he (m:ℕ)(ht:45 ≤m) (x:bed G (d+i'.val) m) : sectorOp L.patch K.K A Ψ R 0 ht d i' i' hs t.eph H (warmEat (m:=m) x.val (atlasF G A.gear hi.1 K.K))=warmEat (m:=m) (wagon L hi.2.1 K.K G _ _ x.val) (atlasF G L.land hi.2.1 K.K):=by
             cases m with| zero=>omega | succ m=>exact hY m ht _ x.property t.eph
         rw [show p.val i'=_ from Ht, show B=boostS (atlasF G L.land hi.2.1 K.K) (-(1/2:ℝ)) (τ i') (d+i'.val) from (by unfold B;rw [hz])]; exact he _ (awareLeaf h i') (x i')
lemma trimU : Edgewise (MotionX H hs t h hi.1 hi.2.1):=by
       intro k z hk i hh; by_cases he:k<3; exact (frontierY H hs h L V hi hp hz t z ⟨k,he⟩ (fun j hJ=>hk _ hJ)).1 i hh; rw [(show trims k z from hk).drop (show 3 ≤ k by omega)|>.limb, map_zero]; rfl
lemma quantit (Λ:Stern K P τ l d w)(hq:L.L=P.L^m)(e:ℕ)(he:e<l+1)(hl:l+1 ≤ i)(x':Tracts G d τ)(z:Phase)(hT:trims z.val x')
   (h':x' z∈(Drift.Turns Λ z).flag e) : (Drift.Turns Λ z).Tap e ((MotionX H hs t Λ.aware hi.1 hi.2.1 x') z)=(lapPrice P.L e)^m • (Drift.Turns Λ z).Tap e (x' z):=by
       have hx:= frontierY H hs Λ.aware L V hi hp hz t x' z (fun i hv=> hT i hv); rw [show MotionX H hs t Λ.aware hi.1 hi.2.1 x' z=_ from hx.2,rope Λ z he]; have hp:= sternCap Λ z; have hu:x' z∈ fillet G _ _ e (by omega):=by
            rw [show fillet _ _ _ _ _= _ from (show fillet _ _ _ _ _=(Drift.Turns Λ z).flag e from (by simp only [Drift.Turns,tuneG,min_eq_left he.le]))]; exact h'
       rw [priceS _ K.K hi.2.1 (K.affordable L.patch) _ (by omega) (by omega) hu (by omega)]; unfold lapPrice; congr 1
       rw[hq, PNat.pow_coe, Nat.cast_pow]; rw [←inv_pow,← pow_mul,mul_comm m,pow_mul] -- inv orientation
end
end YM.OPE.Stroke
