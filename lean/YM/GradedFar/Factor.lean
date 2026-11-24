import YM.GradedFar.Roadway
/-!
# Shape Lipschitz budget on r-normalized kernel moments on BOTH zones

Use the same basis in Sec as throughout. Requires physical hypotheses (see below); including costs and last-leg inverses
from separate G.1--2 charges & G6. Don't hide conversion of `H_s` and `H_r` even for phase prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor
open Fork (Sold Safe)
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
   (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
   (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
variable {hG:G.Simple}{n m h:ℕ}
def toll (u:ListInput G (n+m) h):ℝ:=(2:ℝ)^m*∏ i,width (u i) -- all label input scale factor
private lemma bothScale (A: Both G (Ceiling n h) (Ceiling m h)) (c:ℝ)(hc:0≤c)
    (u:ListInput G n h)(v:ListInput G m h) (H:∀ u v,Box (d:=Ceiling n h) u 1→ Box (d:=Ceiling m h) v 1→‖A u v‖≤c) :
    ‖A u v‖ ≤ c*(∏ i,width (u i))*(∏ i,width (v i)):=by
    refine box_apply (d:=Ceiling m h) (A u) (mul_nonneg hc (Finset.prod_nonneg fun _ _=>width_nn _)) (fun x hx=>?_) v
    let X : MultilinearMap ℂ (fun _ : Fin m=>Sec G h) ℂ →ₗ[ℂ] ℂ:=⟨ ⟨fun f=>f x, fun _ _=>rfl⟩,fun _ _=>rfl⟩; let B:= X.compMultilinearMap A
    exact box_apply (d:=Ceiling n h) B hc (fun u hu=> H u x hu hx) u
section
variable (h)
lemma costs (u: ListInput G n h)(v:ListInput G m h) (r T:ℝ)(A:Both G (Ceiling n h) (Ceiling m h))(c:ℝ)(hc:0≤c)(hp:opField
    (relative J (r*T) r h).toLinearMap≤2)(H:∀ u v, Box (d:=Ceiling n h) u 1 → Box (d:=Ceiling m h) v 1 → ‖A u v‖≤c):
    ‖A u (fun i=> relative J (r*T) r h (v i))‖ ≤ c*toll (repack u v):=by
    have he:= bothScale A c hc u (fun i=> relative J (r*T) r h (v i)) H
    refine he.trans ((mul_le_mul_of_nonneg_left (Finset.prod_le_prod (g:=fun i=> 2*width (v i)) (fun i _=> width_nn _)
        (fun i _=> (op_use (relative J (r*T) r h).toLinearMap (v i)).trans (mul_le_mul_of_nonneg_right hp (width_nn _))))
      (mul_nonneg hc (Finset.prod_nonneg fun _ _=> width_nn _))).trans_eq ?_)
    unfold toll; rw [Finset.prod_mul_distrib, Fin.prod_univ_add]; simp only [repack,Fin.append_left, Fin.append_right,Finset.prod_const,Finset.card_univ,Fintype.card_fin]; ring
end
variable {K:Set (Points n)} {N:Set (Points m)} (hK:IsCompact K)(hx:K ⊆ conf n)(hN:IsCompact N)(hz:N ⊆ Outside m)
variable {I : Type*}{W : Calendar→I→Prop}{z: Calendar→I→Points (n+m)}(hf:∀ p i, W p i → Fits K N p.2 (z p i)){U B:ℝ}
local notation "P∥" => moving G U B
local notation "Π⋆" => fun (p:Calendar)=> wallet G p
local notation "g" => strength G
namespace Road
include hG hK hN hx hz hf
-- AA step from any h Paid G6. G6 h to keep hypotheses cofinal
lemma true_bill {t:ℝ→ℝ} (pay:G1Wide J Z M ν h t U B)
    (H:∃ D:ℝ, G6 F R J (Ceiling n h) (Ceiling m h) h U B D K N) (s:ListInput G (n+m) h)
    (q:Calendar→I→Viewers F): Sold P∥ W (fun i _=>Π⋆ i) (fun _ _=>1) (fun p i=>frank F J (q p i) h p.1 (z p i) s) ∧
    Sold P∥ W (fun i _=> Π⋆ i) (fun p _=>p.1*p.2) (fun p i=>frank F J (q p i) h p.1 (z p i) s-frank F J none h p.1 (z p i) s):=by

    obtain ⟨D,b,hb,T₀,hT,H⟩:=H
    let w (i:Calendar):= b*(g i.1)^(-D); have he:= rpow_paid (U:=U) (B:=B) (hG:=hG) D; obtain ⟨k,hD⟩:=he.exists
    let u:ListInput G n h:=fun i=> s (Fin.castAdd m i)
    let v:ListInput G m h:=fun i=> s (Fin.natAdd n i)
    have hq:= (show repack u v=s from (packing s).symm)
    let y:= toll (repack u v); have hy:0 ≤ y:=mul_nonneg (by positivity) (Finset.prod_nonneg fun _ _=>width_nn _)
    suffices hv:∀ᶠ p in P∥,∀ i,W p i→∀ q: Viewers F,
        ‖frank F J q h p.1 (z p i) s‖ ≤ b*y*wallet G p^k ∧
        ‖frank F J q h p.1 (z p i) s-frank F J none h p.1 (z p i) s‖ ≤ b*y*wallet G p^k*(p.1*p.2) from
      ⟨⟨k,b*y,by positivity,hv.mono (fun p hp i hi=>by rw [mul_one]; exact (hp i hi (q p i)).1)⟩,
       ⟨k,b*y,by positivity,hv.mono (fun p hp i hi=> (hp i hi (q p i)).2)⟩⟩
    filter_upwards [poses (strength_positive hG), poses (show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin),
       poses pay.1,horizonUp (eventually_ge_atTop T₀),poses H,hD, ifWide,funded_forms hK hx hN hz hf]
       with p hg hp ht hv hP hm hw hx i h₁ q'
    specialize ht _ hw; specialize hx i h₁; obtain ⟨x,hx',y',hy',h₂⟩:=hf p i h₁; specialize hP _ hv hw.2 _ hx' _ hy' 0 q'
    rw [h₂] at hx; rw [h₂,← hq, packed F J q' u v 0 hp hx, packed F J none u v 0 hp hx,re_expression,re_expression]
    let A (q:Viewers F):= today F J (d:=Ceiling n h) (e:=Ceiling m h) q 0 p.1 (p.1*p.2) (p.1*p.2) x y'
    have hc:0 ≤ w p:= by dsimp only [w]; positivity
    have hl:(w p)≤ b*(wallet G p)^k:= mul_le_mul_of_nonneg_left hm hb
    have h0:0 ≤ p.1*p.2 := mul_nonneg hp.le (zero_le_one.trans hw.1)
    refine ⟨?_,?_⟩
    · have hf(u' v')(h₁:Box (d:=Ceiling n h) u' 1)(h₂:Box (d:=Ceiling m h) v' 1): ‖A q' u' v'‖ ≤ w p:=by
        obtain hx:=(hP u' v' h₁ h₂).2.1; dsimp only at hx; exact (le_trans ((le_add_of_nonneg_right (width_nn _)).trans
          (le_add_of_nonneg_right (show 0≤rowPrice _ from norm_nonneg _))) hx)
      exact (costs J h u v _ _ _ _ hc ht.2 hf).trans ((mul_le_mul_of_nonneg_right hl hy).trans_eq (by unfold y; ring))
    have hy' (u' v')(h₁:Box (d:=Ceiling n h) u' 1)(h₂:Box (d:=Ceiling m h) v' 1) : ‖(A q'-A none) u' v'‖ ≤ w p*(p.1*p.2):=by
        obtain hx:=(hP u' v' h₁ h₂).2.2; exact (le_add_of_nonneg_right (show 0 ≤ rowPrice _ from norm_nonneg _)).trans hx
    exact (costs J h u v _ _ _ _ (mul_nonneg hc h0) ht.2 hy').trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl h0) hy).trans_eq
      (by unfold y; ring))

lemma payday {α:Future G h}{t:ℝ→ℝ}(plan:PaidFuture F J α t) (pay:G1Wide J Z M ν (h+1) t U B)(ht:Coupling G t)
    (H:∃ D:ℝ,G6 F R J (Ceiling n (h+1)) (Ceiling m (h+1)) (h+1) U B D K N) (s:ListInput G (n+m) h)
    (v: Calendar→ I→ Points (n+m))(q:Calendar→I→Viewers F): Sold P∥ W (fun i _=> Π⋆ i) (fun p x=> ‖v p x‖)
      (fun p i=> stepValue F J (q p i) h p.1 (z p i) (v p i) s):=by
    unfold stepValue; refine Fork.Sold.sum (phys_safety (hG:=hG) (Eventually.of_forall (fun _ _ _=> norm_nonneg _))) (fun i _=> ?_)
    have hp: Sold P∥ W (fun i _=>Π⋆ i) (fun _ _=>1) (fun p j=>frank F J (q p j) (h+1) p.1 (z p j) (update (climbing s) i.1
        (push F J h i.2 p.1 (s i.1)))):=by
        simp_rw [changing _ (climbing s) (push F J h i.2 _ (s i.1))]; refine Fork.Sold.sum (phys_safety (hG:=hG) (Eventually.of_forall fun _ _ _=>zero_le_one)) (fun l _=>?_)
        obtain hv:= (true_bill F J R Z M ν (hG:=hG) hK hx hN hz hf pay H (update (climbing s) i.1 (theory l)) q).1
        obtain ⟨C,hC,hp⟩:= (((plan i.2 (s i.1) l).bounded (Coupling.conforms hG ht))).cost
        obtain h0: Sold P∥ W (fun i _=> Π⋆ i) (fun _ _=>1) (fun (p:Calendar) _=> coord l (push F J h i.2 p.1 (s i.1))) :=
           Fork.Sold.bounded hC ((rising.eventually hp).mono fun i he j _=> he ())
        simpa only [mul_one] using Fork.Sold.mul (phys_safety (hG:=hG) (Eventually.of_forall fun _ _ _=>zero_le_one)) hv h0
    obtain hl: Sold P∥ W (fun i _=>Π⋆ i) (fun p j=>‖v p j‖) (fun p j=> parallel i (v p j)) := Fork.Sold.bounded (c:=1) zero_le_one
        (Eventually.of_forall fun i j _=>by rw [one_mul]; exact shift_cost ..)
    simpa only [mul_one] using Fork.Sold.mul (phys_safety (hG:=hG) (Eventually.of_forall fun _ _ _=>zero_le_one)) hp hl
end Road
end YM.Integration.GradedFar.Tariff
