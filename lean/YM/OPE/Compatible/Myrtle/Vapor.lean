import YM.OPE.Compatible.Myrtle.Plan
/-! # annual R clock for unknown spectators. No ordering between exterior and next period. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Raucous.Host
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge Tree Push Push.AbsoluteSums Precision Matrix Exterior
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra GaussianScore Metric Limn Cinders
variable {G:Gauge}{c f:Side}{I:Type*}
attribute [local instance] Gauge.frobInner
open Radial Flume.Virgin
open PhysicalNext.Repeat.Aroma
open YM.AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom Estimate Sheets Radius.Model
open Woody Next.Free Finset Work.F03 Progress.StationaryScenes AnalyticNext.QuarticMatch.Local Cascade Rill Glass Coin Votive Stationary
variable {i m j:ℕ} {s t r R e d b b' v u z x a C:ℝ}
open Zeph Dew
variable {K:Sponsor G}{T:Seasons K}
structure Studio (L:Host K T) where
       X: Seats L.ForestQ
       w: Bid.Dir G L.c
       ext: AxisChart G L.ForestQ
       Y: Finset (Site L.f)
namespace Studio
variable {L:Host K T} (H:Studio L)
noncomputable abbrev μφ := Jure L H.X
abbrev St := Libra.Keys G (H.X:Type)
noncomputable abbrev V (x:H.St):= VegaP L.Z L.ForestQ H.X H.w H.ext x
noncomputable abbrev Vx(x:H.St):= ‖H.w‖+(‖H.ext‖+‖x‖)
noncomputable abbrev centerA := onset L.Z L.H L.A L.U L.k L.F H.X H.ext H.w
noncomputable abbrev boat(x:H.St):= x+H.centerA
lemma plume(x:H.St): ‖x‖ ≤ H.Vx x ∧ ‖H.V x‖ ≤ H.Vx x:= by unfold Vx V VegaP; refine ⟨ (le_add_of_nonneg_left (norm_nonneg _)).trans (le_add_of_nonneg_left (norm_nonneg _)), (max_le (le_add_of_nonneg_right (add_nonneg (norm_nonneg _) (norm_nonneg _))) ?_)⟩; apply (norm_add_le ..).trans; rw [firmly];exact le_add_of_nonneg_left (norm_nonneg _)
end Studio
-- scoping union
variable {L:I→ Host K T}{Y:∀ i, Studio (L i)}{l:Filter I}{V ε B A T' :I→ℝ}
structure Craft (Y:∀ i,Studio (L i))(l:Filter I) (V:I→ℝ)(A:I→ℝ) (s b e u C:ℝ): Prop where
       light : Tendsto V l atTop
       served : 0<s∧ 0 ≤ b∧ 0<e
       enters : ∀ᶠ i in l, (L i).Rich s b e (A i) u C∧0 ≤ A i
       wage : RateLE l V A 0
       XP : RateLE l V (fun i=>((Y i).Y.card:ℝ)) 0
       IP: RateLE l V (fun i=>((Y i).X.card:ℝ)) 0
       Wax : RateLE l V (fun i=>‖(Y i).w‖) 0
       axe : RateLE l V (fun i=>‖(Y i).ext‖) 0
       covers : ∀ᶠ i in l,∀ x:(Y i).St,ShadeQ (L i).Z (L i).ForestQ ((Y i).V x) (Y i).Y
namespace Craft
variable (h:Craft Y l V A s b e u C)
set_option quotPrecheck false
local notation "μ"=> (fun i=>(Y i).μφ)
include h
lemma jetT : RateLE l V (fun i=>‖(Y i).centerA‖) 0:=by
      let v:=flowerC G s u b C; let p:=porchPrice G u (limbC G s b) C; let r i:=crestPrice G (v*‖(Y i).w‖)+‖(Y i).ext‖; have hk(x:ℝ):= RateLE.const x h.light
      have hp: RateLE l V (fun i=>crestPrice G (p*r i)) 0:=by
            have hx : RateLE l V r 0:=(((hk _).mul ((hk _).mul h.Wax)).mono (le_of_eq (by simp))).add h.axe h.light; exact ((hk _).mul ((hk _).mul hx)).mono (le_of_eq (by simp))
      apply RateLE.of_norm_le hp; filter_upwards [h.enters] with i hi; rw [norm_norm]; obtain ⟨H,-⟩:= hi; let W:= L i; let U:= Y i; obtain ⟨hx,hb,hR⟩:= h.served; let f:=W.F.L.M U.w - U.ext; have hc : ‖(Y i).centerA‖≤ crestPrice G (p* ‖f‖):= H.ripple hx hb hR U.X f; have ht: ‖f‖≤ r i:= le_trans (norm_sub_le ..) (add_le_add_left (H.drift hx hb hR U.w) ‖U.ext‖); exact hc.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (show 0 ≤ p from (H.PourA hx hb hR U.X).pos)) (Nat.cast_nonneg _))
lemma vaulted : Grain μ l V (fun i (p:(Y i).St)=> ‖p‖) 0:=by intro j hj; have hz:=(fun (x:ℝ)=>RateLE.const x h.light); exact ⟨_,((h.IP.mul (hz _)).mul (hz _)).mono (le_of_eq (by simp)),h.enters.mono (fun i ht=> ht.1.DustP h.served.1 h.served.2.1 h.served.2.2 _ _ hj)⟩
lemma shuttled : Grain μ l V (fun i x=>‖(Y i).boat x‖) 0:=by
        apply Grain.of_le ((h.vaulted).add (Grain.const h.jetT) h.light)
        · filter_upwards with i; exact (show Continuous (fun x:(Y i).St=> ‖x+(Y i).centerA‖) by fun_prop).aestronglyMeasurable
        filter_upwards with i; filter_upwards with x; rw[norm_norm]; exact (norm_add_le ..).trans (Real.le_norm_self _)
lemma Vap : Grain μ l V (fun i x=> (Y i).Vx ((Y i).boat x)) 0:= (Grain.const h.Wax).add ((Grain.const h.axe).add h.shuttled h.light) h.light
end Craft
end YM.OPE.Raucous.Host
