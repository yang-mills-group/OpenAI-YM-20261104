import YM.OPE.Compatible.Fathom.Dipper
import YM.OPE.Compatible.Birch.Teasel
/-!
# Support and constants here before n→ ∞ refinement. At k thereafter
per arbitrary precision. Does NOT require quantitative mesh-period modulus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Paver
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d:ℕ}{K:KernelChoices}
open Silt.Float Silt Cloud
local notation "M~"=> TypeFace 1
lemma OpX_uniform (C:KernelChoices)(hp:4 ≤ r): Stock (fun _:Train r=>1) (α:=fun _=>M~) (β:=fun _=>M~) (Op (j:=r) C):=by
       let V:=(heart_saves C.penalty C.penalty_pos hp (fun i:Train r=>i)).1; have hz:=((Stock.constant (ι:= Train r) _ (Whole.boundary 1)).flipped.times V).times (Stock.constant _ (Whole.boundary 1)); simpa only [mul_one,one_mul, Op] using! hz -- inspect
noncomputable def crestR (C:KernelChoices)(P:Train r): Row M~ M~:= minusRows (ShellRow C P) (scaleRows (-1) (composeRows (cobound 0) (transRows (cobound 0))))
lemma splendid (C:KernelChoices)(hp:4 ≤ r): Stock (fun _:Train r=>1) (α:=fun _=>M~) (β:=fun _=>M~) (crestR C):= (OpX_uniform C hp).minus ((Stock.constant _ ((Whole.boundary 0).prod (Whole.boundary 0).flipped)).weight _)
lemma emits (v:Train r)(h:4 ≤ r): (crestR K v).acts n= major (ShellRow K v) n:=by
       let X:=ShellRow K v; let T:= Whole.boundary 0; let D:= composeRows (cobound 0) (transRows (cobound 0)); unfold crestR; rw[(Op_whole (C:=K) h v|>.less (show Whole _ from (T.prod T.flipped).weight _)),acts_scale,T.acts T.flipped, acts_trans]; change X.acts n - -1 • (grad n * (grad n)ᵀ) = _; simp [major,X,ShellRow]
def Elevated (C:KernelChoices)(P:Train r)(u:ℝ):Row M~ M~:= minusRows (crestR C P) (scaleRows (-u) (unitRow M~))
lemma mintedW (C:KernelChoices)(v:Train r)(h:4≤r)(u:ℝ): (Elevated C v u).acts n= major (ShellRow C v) n+u •1:=by
       unfold Elevated; rw [(splendid C h|>.whole v|>.less (((Whole.coin _)).weight _)), emits v h, acts_scale,acts_unit]; simp
lemma amplitude (K:KernelChoices)(h:4≤r){u:ℝ}(hu:0<u): ∃ σ B:ℝ,0<σ ∧0≤B ∧∀ v:Train r,∃ X: Row M~ M~, X.strip σ B ∧∀ n:Side, X.acts n=(major (ShellRow K v) n + u • 1)⁻¹:=by
       have hh: Stock (fun _:Train r=>1) (α:=fun _=>M~) (β:=fun _=>M~) (fun i:Train r=>Elevated K i u):=(splendid K h).minus ((Stock.constant (ι:=Train r) _ (Whole.coin M~)).weight _); obtain ⟨s,a,hs,ha,H⟩:=hh.uniform; let L:=FreeResolvent.margin M~ s a u; have hx:0<L:= margin_pos M~ hs ha.le hu; have he:∀ (v:Train r),∀ n:Side, Gap ((Elevated K v u).acts n) u:=by intro v n; rw [mintedW K v h]; simpa only [zero_add] using! ((show Gap (major (ShellRow K v) n) 0 from ⟨fun x=> by rw [zero_mul]; exact basin_nonneg h v x⟩).shift u)
       choose X Hx hX using fun v=> strip_resolvent (Elevated K v u) (u:=0) le_rfl hu hs ha.le (show _ from (by simpa using H v)) (he v) (show L/2<L from half_lt_self hx); refine ⟨_,_, half_pos hx,le_max_right _ 0,fun v=>⟨X v, strip_mono (Hx v) le_rfl (le_max_left ..),fun n=>by rw[hX,mintedW K v h]; simp only[resolve, zero_smul, add_zero]⟩⟩ -- :=δ+u or u
private lemma mercer (K:KernelChoices) (ε:ℝ) (he:0<ε)(h:4≤r):∃ s B:ℝ, 0<s∧∃ V:Train r→Row M~ M~, (∀ i,(V i).strip s B) ∧ ∀ᶠ n:Side in comap PNat.val atTop,∀ v,∀ i j:Body 1 n,‖lineC (ShellRow K v) n i j-(V v).acts n i j‖<ε:=by
      let l:Filter Side:= comap PNat.val atTop
      obtain ⟨d,hd,H⟩:= tree_cost K h
      obtain ⟨u,hu,h⟩:∃ u>0,d*Real.sqrt u<ε:=by
           let a:=ε/(d+1); have ha:0<a:=div_pos he (by positivity); refine ⟨a^2,pow_pos ha _,?_⟩; rw [Real.sqrt_sq ha.le]; unfold a; field_simp; nlinarith only [he]
      obtain ⟨s,B,hs,hQ,HQ⟩:= amplitude K ‹4≤r› hu; choose V hX hV using HQ; have hB: Tendsto (fun n:Side=> d*Real.sqrt u+ aquas n *u⁻¹) l (𝓝 (d*Real.sqrt u)):= by convert (worldZ id (show Tendsto PNat.val l atTop from tendsto_comap) u⁻¹).const_add (d*Real.sqrt u) <;> simp
      refine ⟨s,B,hs,V,hX,?_⟩; filter_upwards [hB.eventually (eventually_lt_nhds h)] with k hk v i j; rw [hV,norm_sub_rev]; exact (H v u hu k i j).trans_lt hk
lemma windward (K:KernelChoices) (ε:ℝ)(x y:M~)(i:Cover) (he:0 < ε) (h:4 ≤ r): ∀ᶠ n:Side in Filter.comap PNat.val atTop,∀ v:Train r,‖vein v K x y i n 0-Spill K v h x y i‖≤ ε:=by
       let L:=Filter.comap PNat.val (atTop (α:=ℕ)); let q:=ε/3; obtain ⟨s,B,hs,V,hV,H⟩:=mercer K q (by unfold q; positivity) h; have ht(v:Train r): ‖Spill K v h x y i-V v x y i‖≤ q:= by
            apply le_of_tendsto (((guessed (C:=K) v h x y i).sub (pocket tick2 (V v) (show Whole _ from ⟨s,B,hs,hV v⟩) born x y i (fun _=>0))).norm); filter_upwards [(show Tendsto tick2 atTop L from tendsto_comap_iff.mpr born).eventually H] with n hn; exact (hn ..).le
       have hv:Tendsto (fun i:Side=> q*(i.val:ℝ)) L atTop:= (tendsto_natCast_atTop_atTop.comp (show Tendsto PNat.val L atTop from tendsto_comap)).const_mul_atTop (by unfold q;positivity); let Z:= 2*Flume.poise 1 i* widthCost s 1*B
       filter_upwards [H,hv.eventually_ge_atTop Z] with n hn hi v; let A:=(V v).acts n (0,x) (0+wrap n i,y); let Y:= V v x y i; have he:‖A-Y‖≤ q:=by
            apply le_of_mul_le_mul_left (a:=(n.val:ℝ)); · have h:=coefWind (V v) (hV v) hs (N:=n) x y i 1; simp only [pow_one] at h; unfold A; rw [zero_add]; exact h.trans (hi.trans_eq (mul_comm ..))
            exact Nat.cast_pos.mpr n.pos
       let x':=vein v K x y i n 0; let y':=Spill K v h x y i; change ‖x'-y'‖ ≤ _; rw [show x'-y'= (x'-A)+(A-Y)+(Y-y') by abel]; refine ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add (hn v _ _).le he)) ((norm_sub_rev Y y').trans_le (ht v)))).trans_eq ?_; unfold q;ring -- specify
end YM.OPE.Cascade.Paver
