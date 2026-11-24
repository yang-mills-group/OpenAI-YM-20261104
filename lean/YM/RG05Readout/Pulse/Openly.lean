import YM.RG05Readout.Pulse.Excursion
/-! Actual allowed domain and silent alternatives (at full tensor aperture),
not masking collisions by fiat. Provide morphology for stencil expansion in
support lanes.Angles threshold inclusive. This applies only to rel geometry,
no detecting restrictions assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Pulse
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{I J V:Type}[DecidableEq V][Fintype V]
    {j b k D:ℕ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "A"=> C.S.a
local notation "Λ"=> C.S.toDepth
local notation "X!"=> C.side N p
local notation "Y!"=> C.side b p
local notation "G!"=>C.S.gridPoint
local notation "o!"=> C.S.place
local notation "ρ₀"=>C.S.radius p
local notation "W!"=> Wave V
local notation "J!"=> Cloud V
section morph
variable (h:b ≤ N)(s:V→ℕ)(v:(i:V)→Palette C (s i))(q:ℝ)(Ψ: Wave V)(hq:0<q)
variable {R:ℝ} (hΨ:∀ x∈tsupport Ψ.val,∀ i:V, ‖x i‖≤R)
local notation "r"=> Λ h p
local notation "T"=> Site (r).count
abbrev men (b p t:ℕ)(u:Site (C.side b p)):Prop:= separation u 0 ≤ t
noncomputable def area (t:ℕ):Finset (V→ Site (C.side b p)):= Finset.univ.filter (fun x=> ∀ i,separation (x i) 0 ≤ t)
include hΨ hq
omit [DecidableEq V] in
lemma understood (w:V→ T)(x:E4)(hx:x∈Native.box)(u:V→Site Y!)
    (he: (fun i=> q⁻¹ • (o! (u i)- (A b) • x) + (q⁻¹*A b) • placeR (r) (w i))∈ tsupport Ψ.val): ∀ i:V,(A b)*(separation (u i) 0) ≤ q*R+2*A b:=by
    intro i; refine (Ribbons.normC _ _ _ _).1.trans ?_; let y:= placeR (r) (w i); have hu:y∈ Native.box:= by simpa only [smul_zero,add_zero] using mapsR (r) (C.S.toDepth_odd h p) (w i) Native.box0
    refine (bill (C:=C) (b:=b) x (lift (u i)) y hu hx).trans (add_le_add ?_ le_rfl); apply aperture _ R _ _ hq
    convert (hΨ _ he i) using 2; rw [mul_smul,← smul_add]; congr 1; unfold y; change o! (u i)+ _-_=o! (u i)-_ + _; abel
lemma asleep (t:ℕ)(u: V→Site Y!)(hp:u ∉ area (C:=C) (p:=p) (b:=b) t)(hR: q*R+2*(A b) ≤ (A b)*(t:ℝ)) (g:Body): meet s v q Ψ h u g=0:=by
    funext U'; let l:=scalp (C:=C) s v u h
    have he'(x)(hx:x∈Native.box): l (cropX Ψ u q x)=0:=by
        unfold l scalp cropX; simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply, fly_fork]; apply sum_eq_zero
        intro w _; let z:= fun i:V=> (r).assemble (u i,w i)
        rw [taboo]; exact smul_zero _
        intro hP; apply hp; apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _,fun i=>?_⟩
        exact_mod_cast (le_of_mul_le_mul_left ((understood h q Ψ hq hΨ w x hx u hP i).trans hR) (C.S.a_pos b))
    unfold meet; rw [setIntegral_congr_fun (g:=fun _=>0) Pert.Cellular.cells_compact.measurableSet (fun x hx=>by rw [show scalp s v u h _=0 from he' x hx,Pi.zero_apply,mul_zero]),integral_zero];rfl
lemma stanza (t m:ℕ)(hR:q*R+2*(A b) ≤ (A b)*(t:ℝ)) (g:Body): constellation s v q Ψ h m g=premiums C s m b q • ∑ i∈ area (C:=C) (p:=p) (b:=b) t,meet s v q Ψ h i g:= congr_arg (premiums C s m b q • ·) (sum_subset (subset_univ _) (fun i _ hx=>asleep h s v q Ψ hq hΨ t i hx hR g)).symm
omit hΨ hq
open Set
lemma area_cost (t:ℕ): (area (C:=C) (p:=p) (b:=b) (V:=V) t).card ≤ ((Lattice.box t).card)^(Fintype.card V):=by
   let I:=area (C:=C) (p:=p) (b:=b) (V:=V) t; let f:= fun (x:V→Site Y!)(i:V)=> lift (x i); have hv: Function.Injective f:=by intro x y hp; funext i; conv_lhs=> rw [←wrap_lift (x i)]; exact congr_arg (Lattice.wrap Y!) (show lift (x i)=lift (y i) from congr_fun hp i) |>.trans (wrap_lift _)
   let T₁ := Fintype.piFinset (fun _i:V=> Lattice.box t); have hP(i)(he:i∈I) : f i∈ T₁:= Fintype.mem_piFinset.mpr (fun j=>by refine (show lift (i j)∈ Lattice.box t from ?_); have ht: separation (i j) 0 ≤ t:=(Finset.mem_filter.mp he).2 j; unfold separation at ht; rw [sub_zero] at ht; rw [box_test]; constructor <;> intro a <;> (have := (component_le (i j) a).trans ht; omega))
   have he: I.image f ⊆ T₁:=by rintro i hi; obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hi; exact hP j hj
   have hi:= Finset.card_le_card he; rw [Finset.card_image_of_injective _ hv] at hi; unfold T₁ at hi; rw [Fintype.card_piFinset] at hi; simp only [prod_const,card_univ] at hi; exact hi
end morph
end YM.RG05Readout.Pulse
