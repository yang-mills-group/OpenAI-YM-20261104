import YM.GradedFar.Render
/-!
# No new orientation after changing Caps.

`Axil` & `Connected`: the genuine filtration and unit etc requirements on the P operand in
`frank`; permit all the `Held.permitted` expense without assuming any scale estimates.
Use on Leading and its prescribed H actual frame.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Billboard
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open YM.Integration.GradedFar.Neighbor YM.Integration.GradedFar.Tariff.Playbill
open Climb Maxwell Maxwell.Free
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J P:ℝ→tower S){h:ℕ}
-- orientation at each cap; separate inclusion in application because it concerns both caps
structure Axil (r:ℝ)(h:ℕ) : Prop where
    unit : assign J r h (leaf G h)= S.unit h
    real v: assign J r h (reel h v)= S.conj F.room.kernel.spin h (assign J r h v)
    heel v (s:Signed): assign J r h (ori s.ortho h v)= S.mirror F.room.kernel.spin h s (assign J r h v)
local notation "V" => Sec G h
abbrev Connected : Prop := ∀ h, ∀ d, ∀ he: d ≤ h, Included F J d h he
-- from original Leading & later alignment
local notation "L"=> Maxwell.Free.fields C.labels h
variable (C)
-- avoid local macros in variable declarations
lemma eng_unit (h:ℕ):fields C.labels h ((Bel C.book).unit h)=leaf G h:=Subtype.ext (unit_address ..)
lemma eng_star (v:(Bel C.book).Field h) : fields C.labels h ((Bel C.book).conj (spin_free C.labels) h v)= reel h (L v):= Subtype.ext (address_star ..)
lemma eng_turn (v:(Bel C.book).Field h)(s:Signed): fields C.labels h ((Bel C.book).mirror (spin_free C.labels) h s v)=ori s.ortho h (L v):= Subtype.ext (address_motion ..)
lemma eng_rise {d:ℕ}(hv:d≤h)(v:(Bel C.book).Field d): fields C.labels h ((scheme C.labels).rise hv v)=up hv (fields C.labels d v):= Subtype.ext (address_rise ..)
variable {C}
lemma axile (H:Leading F J)(h:ℕ):∀ᶠ r in trail, Axil F J r h:=by
 filter_upwards [H.equivariant h,H.unit h] with r hr H; let U:= assign J r h
 have he (v): assign J r h ((fields C.labels h) v)= J r h v:= by rw [assign, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
 constructor
 · rw [← eng_unit C,he]; exact H
 · intro v; obtain ⟨w,rfl⟩:= (fields C.labels h).surjective v; rw [← eng_star C,he,he]; exact hr.2 _
 · intro v s; obtain ⟨w,rfl⟩:= (fields C.labels h).surjective v; rw [← eng_turn C,he,he]; exact hr.1 _ _
lemma include_j {d:ℕ}(hv:d≤h)(H:∀ᶠ r in trail,∀ v:(Bel C.book).Field d,J r h ((scheme C.labels).rise hv v)= F.sector.derivatives.rise hv (J r d v)) : Included F J d h hv:=by
    filter_upwards [H] with r hr v; obtain ⟨v,rfl⟩:= (fields C.labels d).surjective v
    rw [← eng_rise C,assign,assign, LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply,LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]; exact hr _
lemma axial_preserved (r:ℝ) (H:Axil F J r h)(B:Normalize.Change G h)
    (hu:∀ v:V, assign P r h v= assign J r h (stand B v)): Axil F P r h:= by
    refine ⟨ by rw [hu,solitary,H.unit],fun v=>?_,fun v s=>?_⟩
    · rw [hu,hu,← stood_reel,H.real]
    rw [hu,hu,← stood_ori,H.heel]

lemma home_path {d:ℕ}(hv:d≤h)(wt:Included F J d h hv): ∀ᶠ i in clock,∀ v:Sec G d,
    relative J i.1 (next i) h (up hv v)=up hv (relative J i.1 (next i) d v):=by
 filter_upwards [running.eventually wt,nextPath.eventually wt] with i hi hk v; apply (assign J i.1 h).injective
 rw [atHome,hi, atHome,hk]
lemma allot (h0: ∀ d, ∀ (he:d≤h), Included F J d h he)(hx:∀ᶠ r in trail, Axil F J r h): ∀ᶠ p in clock,
    stripe J h p-1∈Normalize.Change G h:=by
 filter_upwards [eventually_all.mpr (fun i:Fin (h+1)=> home_path F J (Nat.le_of_lt_succ i.isLt) (h0 _ _)),
   running.eventually hx,nextPath.eventually hx] with p hr he hs
 let f:=stripe J h p; let r:=p.1; let s:=next p; let D:=Level.Dial (G:=G) h (Real.log (stretch p)); let U:=relative J r s h
 have Hpq(x):f x=D (U x):=rfl
 have h₁: U (leaf G h)= leaf G h:= (assign J r h).injective ((atHome J ..).trans (hs.unit.trans he.unit.symm))
 have h₂(x:V): f (reel h x)=reel h (f x):=by
    rw [Hpq, Hpq]; have hu:U (reel h x)= reel h (U x):= by
      apply (assign J r h).injective; -- cover rewrite rest
      unfold r U; rw [he.real (U x),atHome J,hs.real _,atHome];
    rw [hu]; exact Level.Dial_real ..
 have h₃(x:V)(s':Signed): f (ori s'.ortho h x)= ori s'.ortho h (f x):=by
    rw [Hpq, Hpq]; have hu: U (ori s'.ortho h x)=ori s'.ortho h (U x):= by
      apply (assign J r h).injective; unfold r U; rw [he.heel,atHome J,hs.heel,atHome]
    rw [hu]; exact Level.Dial_ori ..
 rw [may_change]; refine ⟨?_,fun d hv m hx=>?_,?_,?_⟩
 · change f (leaf G h)- leaf G h=0; rw [Hpq,h₁, show D (leaf G h)=_ from Level.Dial_leaf (Real.log (stretch p)),sub_self]
 · 
   let z:Sec G d:=⟨m.val,hx⟩; have hz : m=up hv z:=rfl
   apply Submodule.sub_mem _ _ hx; have hx: f m=(up hv) (Level.Dial d (Real.log (stretch p)) (relative J r s d z)):= by
     rw [Hpq,hz]; have hr:= hr ⟨d,Nat.lt_succ_of_le hv⟩ z; rw [show U (up hv z)=_ from hr]; exact Level.chain ..
   change (f m).val∈ _; rw [hx]; exact (Level.Dial d (Real.log (stretch p)) (relative J r s d z)).property
 · intro p; change _=reel h (f p-p); rw [map_sub]; exact congrArg (·-reel h p) (h₂ p)
 intro s p'; change _=ori s.ortho h (f p'-p'); rw [map_sub]; exact congrArg (·-ori s.ortho h p') (h₃ p' s)
end YM.Integration.GradedFar.Tariff.Billboard
