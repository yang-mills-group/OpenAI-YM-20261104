import YM.OPE.Compatible.Ibis.Shroud
import YM.OPE.Compatible.Sward.Lucent
/-! # Probe numeric tensor coefficients independent of site sizes. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Ibis
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{K: KernelChoices}{I:Type}{i j k m:ℕ}{n:Side}{ε v s r R A:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals
section Quest
noncomputable abbrev UpΩ (K:KernelChoices)(i:ℕ)(h:4 ≤ i) := (upperWind K h).choose
noncomputable def Tale_B (G:Gauge)(n:Side)(i:Tab (Shade G) n): Bid.Dir G n:= (flats G n).symm (Pi.single (station G n i) 1)
variable (V:Train i)(h:4 ≤ i)
lemma StakeQ : Quest (Tale_B G n) (Vessel K V G n h) (UpΩ K i h+1):=by
       let P:=Vessel K V G n h; let U(k:Tab (Shade G) n):= Tale_B G n k; let F:= flats G n; let a:= UpΩ K i h; have ha:a>0:=(upperWind K h).choose_spec.1
       have hh(k): P.P (U k) (U k) ≤ a+1:=by
             obtain ⟨l,j⟩:=k; let b:FreeResolvent.Slot G n 1:= station G n (l,j); let c:= Shrink K G V n; let p: Body 1 n := (b.1,b.2.1); have ht:F (U (l,j))=Pi.single b 1:= F.apply_symm_apply _; rw [show P.P _ _= _ from (Hport K V G n h).choose_spec.2 _ _,ht, single_one_dotProduct,mulVec_single_one]; change c b b≤ _; have hc:c b b= (major (ShellRow K V) n) p p+ Resolvent.missing n p p:=by change (if b.2.2=b.2.2 then _ else _)= _; rw [if_pos rfl];rfl
             have hu: Resolvent.missing n p p≤ 1:=by unfold p; rw [Resolvent.projected,if_pos rfl]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast n.pos))
             apply hc.trans_le; refine add_le_add ?_ hu; have hp:= (upperWind K h).choose_spec.2 V n (Pi.single p 1); rw [single_one_dotProduct,mulVec_single_one,single_one_dotProduct,Pi.single_eq_same,mul_one] at hp; exact hp
       refine ⟨by linarith only [ha],fun x y=>?_⟩; obtain ⟨p,hp,hT⟩:=P.slope; let a':=U x; let b':=U y; have hx(k):0≤ P.P k k := (by linarith only [mul_nonneg hp.le (sq_nonneg ‖k‖), hT k]); have hV:= hx (a'-b'); have hL:= hx (a'+b'); have hS:= hh x; have hs:=hh y; rw [P.P.map_sub,LinearMap.sub_apply,map_sub,map_sub,P.turns a' b'] at hV; rw [P.P.map_add,LinearMap.add_apply,map_add,map_add] at hL; change ‖P.P a' b'‖≤ a+1; rw[Real.norm_eq_abs,abs_le]; exact ⟨by linarith only[hS,hs,P.turns a' b',hL],by linarith only[P.turns a' b', hS,hs,hV]⟩
local notation "wP"=> Tale_B G n
lemma B_hat(t: Tab (Shade G) n): deckW G n (flats G n (Tale_B G n t))=Pi.single t 1:=by
       funext i; rw [Tale_B,ContinuousLinearEquiv.apply_symm_apply]; change (Pi.single (station G n t) 1: Vec G n 1) (station G n i)= (Pi.single t 1:deck (Shade G) n) i; by_cases ht:i=t; · subst i; simp only [Pi.single_eq_same]
       rw [Pi.single_eq_of_ne ((station G n).injective.ne ht), Pi.single_eq_of_ne ht]
lemma spotlight (x:Site n)(p:Seat k m (Shade G))(hp:settled (m:=m) p)(y:Fin j→Tab (Shade G) n)
       (hs: Spectre (Vessel K V G n h) (Chart.tangent G (Body 1 n)) (LightP x (m:=m) p) j s):
       let q:= boostS (rentV G V h K n) (1/2) m k p; ‖scribe x (lilies m k _ q j) (fun i=>Pi.single (y i) 1)‖ ≤ s*Fortune (UpΩ K i h+1) j 0 2:=by
            intro q; let v:= wP ∘ y; let A:= Vessel K V G n h; let μ:=Chart.tangent G (Body 1 n); let z:=(flats G n).toContinuousLinearMap; let F:=formSong m k G x q; let P:= Dawn μ A (LightP x (m:=m) p); have hh:F∈ harmon _ k:= chic x q (turfy _ _ _ hp); have he:P= Strike k F ∘ z:=by rw [show P=LightP x (m:=m) q from wellD x p V h hp]; exact funext fun i=> (strikesT q x i).symm
            have hc:= (polW x (m:=m) p).cost; have hV: F j (z ∘ v)=(Tensor.coeff P j 0 v):=by rw [he, onceD, gradeC hh]; exact (sailCost F k).cost -- rewrite expects application
            have hf : deckW G n ∘ z ∘ v= fun i=>Pi.single (y i) 1:= funext fun i=> B_hat ..
            rw[← hf, ← tensors, hV, show Tensor.coeff P j 0 v=((j.factorial:ℝ)⁻¹)*Vas A μ (LightP x (m:=m) p) v from veronica A μ _ hc v,norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (by rw [norm_inv,Real.norm_natCast]; exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Nat.factorial_pos _)))).trans (hs.runs _ (StakeQ V h (G:=G) (n:=n)) le_rfl (Stature.poly hc j) y)
end Quest
end YM.OPE.Ibis
