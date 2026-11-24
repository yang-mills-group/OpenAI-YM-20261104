import YM.RG05Readout.Pulse.Writer
/-! Active support listener for physical branch.Rel profile held.
 All upper choices touched by projection for a tested slot, verifying
 regrouping/reclosure applicability to valuation on original data again.
 Distinct slot stencils may share roots. -/
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
section survey
lemma taboo (q:ℝ) (s:V→ℕ)(v:(i:V)→Palette C (s i))(z:V→ Site X!)(f: Wave V)(y:J!)(h:y ∉ tsupport f.val): harpoon (C:=C) (p:=p) (N:=N) s v z (fork q y f)=0:=by
    have he:∀ i,pie f 0 i y:=fun i=> by
        unfold pie; rw [show iteratedFDeriv ℝ i f.val y=0 from notMem_support.mp (fun hh=>h (support_iteratedFDeriv_subset i hh)),show (0:W!).val=(0:J!→ℂ) from rfl];simp
    rw [stung s v z (fun i _=>he i),map_zero,map_zero]
lemma room_B (u:E4)(h:u∈ Native.box): ‖(C.S.a b) • u‖≤ C.S.a b:=by rw [norm_smul,Real.norm_of_nonneg (C.S.a_pos _).le];exact mul_le_of_le_one_right (C.S.a_pos _).le (Pert.Cellular.cells_bd h)
lemma aperture (q K:ℝ) (x y:E4)(h:0<q)(hx: ‖q⁻¹ • (x-y)‖≤ K): ‖x-y‖≤q*K:=by
   rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr h).le, mul_comm,←div_eq_mul_inv,div_le_iff₀ h,mul_comm] at hx; exact hx
variable (h:b ≤ N){q B R:ℝ}
local notation "r"=> (Λ h p)
local notation "T"=> Site (r).count
local notation "K!"=> (r).count.val
variable (z:Site (C.side b p))(x:E4)(hx:x∈Native.box)(o:Site (C.side b p))
-- offsets supported.Far tests.B radius.F.any
noncomputable def offset (i:T):= K! • (lift o+lift z)+ lift i
local notation "t₀"=> voyager C p b z x
local notation "v"=> offset h z o
local notation "U"=> fun j:T=> (r).assemble (o+z,j)
-- equation trace
lemma actual_offset (i:T): Lattice.wrap _ (v i)=U i:=by rw [offset, ← grid_wrap h, map_add,wrap_lift,wrap_lift]
lemma relatives (w:Cover) (i:T): (G! b w+A b • placeR (r) i)-A b • x= G! N (K! • (w+lift z)+ lift i) - t₀:=by rw [← grid_pair h,Work.B16.grid_add, voyager]; change _=_+ o! z+ _-_; abel
lemma from_lift (i:T)(hB: ‖t₀‖≤B)(he:‖G! N (v i)-t₀‖ ≤R)(hp:B+R<ρ₀) : lift (U i)= v i:=by
    apply reads_grid (actual_offset h z o i)
    let X:=G! N (v i); have hi:=norm_add_le (X-t₀) (t₀); rw [sub_add_cancel] at hi
    exact lt_of_le_of_lt (hi.trans (add_le_add he hB)) (by rw [add_comm]; exact hp)
lemma bill (w:Cover)(u:E4)(hu:u∈ Native.box)(hx:x∈Native.box) : ‖G! b w‖ ≤ ‖(G! b w+ A b • u)- A b • x‖+2*(A b):=by
    let y:= A b • u; let z':= A b • x; let Δ:=G! b w+y; have ht:Δ= (Δ-z')+z':= (sub_add_cancel _ _).symm; have hΔ:‖Δ‖≤ ‖Δ-z'‖+‖z'‖:=by nth_rw 1 [ht];exact norm_add_le ..
    linarith only [hΔ,Flatten.norm_le_insert (G! b w) y,show ‖y‖≤A b from room_B u hu,show ‖z'‖≤ A b from room_B x hx]
include hx
lemma from_root (i:T)(he:‖o! (U i) - t₀‖≤ R)(hp: R+ 2*A b < ρ₀) : lift (U i)= v i:=by
    let y:= U i; obtain ⟨w',hw,hW⟩:=ascent h y; rw [show (r).residue y=i from (r).assemble_res ..] at hW; let w:=w'-lift z; have hP: Lattice.wrap Y! w=o :=by unfold w; rw [map_sub,hw,(r).assemble_parent,wrap_lift]; exact add_sub_cancel_right .. 
    let b':= placeR (r) i; have hv:b'∈Native.box:= by simpa only [smul_zero,add_zero] using mapsR (r) (C.S.toDepth_odd h p) i Native.box0
    have h': G! b w+A b • b'-A b • x=o! y- t₀:=by rw [show G! b w+A b • b'-A b • x=_ from relatives h z x w i, Schedule.place,hW,show w+lift z=w' from sub_add_cancel ..]
    have hg:= reads_grid hP (lt_of_le_of_lt ((bill (C:=C) (b:=b) x w b' hv hx).trans (by rw [h']; exact add_le_add he le_rfl)) hp); unfold offset; rw [hg,show w+lift z=w' from sub_add_cancel ..]; exact hW
end survey

section crossed
variable (h:b ≤ N)(s:V→ℕ)(v:(i:V)→Palette C (s i))(Ψ: Wave V)(u:V→Site (C.side b p))
local notation "r"=> Λ h p
local notation "T"=> Site (r).count
local notation "S"=> scalp (C:=C) s v u h
local notation "q!"=> (fun o:V→Site X!=> harpoon (C:=C) (N:=N) (p:=p) s v o)
-- Relative packet in shape Φ on support
variable (q:ℝ)(hq:0<q)
noncomputable def cropX (x:E4):= fork (q⁻¹*A b) (fun i:V => q⁻¹ • (o! (u i)-A b • x)) Ψ
local notation "Z"=> fun x=> cropX Ψ u q x
noncomputable def cameo (C:Family G)(p N:ℕ)(q:ℝ)(Ψ:Wave V)(y:E4)(w:V→ Site (C.side N p)):= fork (q⁻¹*C.S.a N) (fun i:V=> q⁻¹ • (C.S.place (w i)-y)) Ψ
local notation "M!"=> cameo C p N q Ψ
-- compute through a projected slot root tuple. z base center
variable {B R:ℝ}(hΨ:∀ x∈tsupport Ψ.val,∀ i:V, ‖x i‖≤R)(z:Site (C.side b p))(x:E4)(hx:x∈Native.box)(hz:‖voyager C p b z x‖≤ B)
local notation "K!"=> (r).count.val
local notation "t₁"=> voyager C p b z x
local notation "U"=> fun w:V→T=> (fun i:V=> (r).assemble (u i+z,w i))
local notation "V!"=> fun w:V→T=> (fun i:V=> offset h z (u i) (w i))
local notation "Φ"=> fun w:V→T=>fork ((↑K!:ℝ)⁻¹) (fun i:V=>placeR (r) (w i)) (Z x)
omit [DecidableEq V] in
lemma mask_test (w:V→T) : Φ w = fork (q⁻¹*A N) (fun i=>q⁻¹ • (G! N (V! w i)-t₁)) Ψ:=by
   dsimp only [cropX]; rw [fly_fork]; 
   apply congr_arg₂ (fun a (b:J!) => fork a b Ψ)
   · let t:ℝ:=K!; change q⁻¹*A b*t⁻¹=q⁻¹*A N; rw [← C.S.embeds_scale (Λ h p),mul_assoc,mul_assoc,mul_inv_cancel₀ (by positivity),mul_one]
   funext i; change q⁻¹ • (o! (u i)- A b • x) + (q⁻¹*A b) • placeR (r) (w i)=_
   rw [mul_smul,← smul_add]; apply congr_arg (q⁻¹ • ·); unfold offset; rw [← relatives h z x]; change o! (u i)-A b • x+A b • placeR _ _=o! (u i)+ _-_; abel
include hΨ hx hq hz
lemma diving (w:V→T)(hp:q*R+2*(A b)<ρ₀)(hρ:B+q*R<ρ₀): harpoon (C:=C) (N:=N) (p:=p) s v (U w) (Φ w)= harpoon (C:=C) (N:=N) (p:=p) s v (U w) (M! t₁ (U w)):=by
   rw [mask_test]; unfold cameo; let W:=(U w); let a :=fun i:V=> q⁻¹ • (G! N (V! w i)- t₁); let b': J!:=fun i=> q⁻¹ • (o! (W i)- t₁); change q! W (fork _ a Ψ)= q! W (fork _ b' Ψ)
   by_cases he: a∈tsupport Ψ.val
   · have hE: b'=a:=by funext i; unfold b' Schedule.place; rw [show lift (W i)= (V! w i) from from_lift h z x _ _ hz (aperture q R _ _ hq (hΨ _ he i)) hρ]
     rw [hE]
   by_cases hg:b'∈ tsupport Ψ.val
   · have hE:b'=a:=by funext i; unfold b' Schedule.place; rw [show lift (W i)= (V! w i) from from_root h z x hx _ _ (aperture q R _ _ hq (hΨ _ hg i)) hp]
     rw [hE]
   exact Eq.trans (taboo _ s v W _ _ he) (taboo _ s v W _ _ hg).symm
end crossed
end YM.RG05Readout.Pulse
