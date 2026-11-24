import YM.RG05Readout.Flatten.Village
/-! Link of tree test through the seam chart. Recovery of actual field TEST
requires not dropping boundary roots w/o verifying any missed terms vanish.
Period representatives earlier are Seam/Schedule right-closed. Use strict
chart margin from Physical support; no implicit periodic extension here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Flatten
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow
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
open GridApprox
lemma grid_for (h:j ≤ b) (z:Cover)(x:Site (Λ h p).count)(w:E4):
   G! j z+A j • (placeR (Λ h p) x+ (↑(Λ h p).count.val:ℝ)⁻¹ • w)= G! b ((Λ h p).count.val • z+ lift x)+ A b • w:=by
   let r:=(Λ h p); apply PiLp.ext; intro i
   let t:= r.count.val; change (A j)*(z i:ℝ)+ (A j)*((t:ℝ)⁻¹*(lift x i:ℝ)+ (t:ℝ)⁻¹*w i)= (A b)*((t • z i+ lift x i:ℤ):ℝ)+ (A b)*w i
   rw [nsmul_eq_mul]; have h_t:(t:ℝ) ≠ 0:=by exact_mod_cast r.count.property.ne'
   rw [← show A b*(t:ℝ)=_ from C.S.embeds_scale r]; push_cast; field_simp; ring
lemma grid_pair (h:j ≤ b)(z:Cover)(x:Site (Λ h p).count): G! j z+A j • placeR (Λ h p) x= G! b ((Λ h p).count.val • z+lift x):=by
    simpa only [smul_zero,add_zero] using grid_for h z x 0
lemma grid_wrap (h:j ≤ b)(z:Cover)(x:Site (Λ h p).count): let r:=(Λ h p); r.assemble (Lattice.wrap _ z,x)=Lattice.wrap _ (r.count.val • z+ lift x):=by
    intro r; unfold Ratio.assemble; rw [Ratio.embed_wrap,map_add]
lemma reads_grid {u:Site Y!}{v:Cover}(h:Lattice.wrap _ v=u)(hp:‖G! b v‖<ρ₀) : lift u=v := by
   rw [lift_eq_iff]; refine ⟨h.symm,fun i=>?_⟩
   have hx: ‖G! b v‖ < A b*(C.side b p).val/2:=by rw [C.S.span_side]; exact hp
   have ht:=PiLp.norm_apply_le (G! b v) i
   change |A b*(v i:ℝ)| ≤ _ at ht
   obtain ⟨h₁,h₂⟩:= abs_lt.mp (ht.trans_lt hx); have hb:= C.S.a_pos b
   constructor
   · exact_mod_cast (lt_of_mul_lt_mul_left (a:=A b) (show A b*(-((C.side b p).val:ℝ)) < A b*(2*(v i:ℝ)) from by linarith) hb.le)
   exact_mod_cast (lt_of_mul_lt_mul_left (a:=A b) (show A b*(2*(v i:ℝ))< A b*(C.side b p).val from by linarith) hb.le).le
lemma ascent (h:j≤ b)(y:Site Y!): let r:=(Λ h p); let x:= lift (r.residue y)
   ∃ w':Cover, Lattice.wrap _ w'=(Λ h p).parent y ∧ lift y=(r.count.val • w')+x:=by
    intro r x; let z:=lift y-x; have ht: (Lattice.wrap r.count) z=0:=by unfold z x; rw [map_sub,wrap_lift,← r.residue_wrap,wrap_lift,sub_self]
    have hv (i:Axis): (r.count.val:ℤ) ∣ z i:= (ZMod.intCast_zmod_eq_zero_iff_dvd ..).1 (congr_fun ht i)
    choose w hw using hv; have hζ:z=r.count.val • w:= by funext i; change _= r.count.val • w i; rw [nsmul_eq_mul,hw]
    have hv':lift y=r.count.val • w+x:=sub_eq_iff_eq_add.mp hζ
    refine ⟨w,?_,hv'⟩; have he : r.assemble (Lattice.wrap _ w,r.residue y)=y:=by rw [grid_wrap,← show lift y= r.count.val • w+ lift (r.residue y) from hv', wrap_lift]
    exact (show r.parent y=Lattice.wrap _ w from (congr_arg r.parent he).symm.trans (Ratio.assemble_parent ..)).symm
-- core test link. If either stencil can fire against Φ, there is no wrap.
def restricted (C:Family G)(b p:ℕ)(z:Site (C.side b p)):Body →ₗ[ℂ] Body:= Native.pull (C.S.place z) (C.S.a b)
local notation "F!"=> restricted C b p
local notation "F0"=> restricted C j p
lemma norm_le_insert (a b:E4): ‖a‖ ≤ ‖a+b‖+‖b‖:= (le_of_eq (congr_arg Norm.norm (add_sub_cancel_right a b).symm)).trans (norm_sub_le ..)
lemma linkR(h:j≤b)(f:Body){R:ℝ}(hf: ∀ x∈tsupport f.val, ‖x‖≤R)(hR:R+A j*3 < ρ₀)(y:Site Y!)(k:ℕ):
   let r:=(Λ h p); let i:=r.residue y; let g:= feeR r i (F0 (r.parent y) f); let g':=F! y f
   g=g' ∨ Cap k g 0 ∧ Cap k g' 0:=by
   intro r i g g'; let z:= r.parent y
   obtain ⟨w,hw,hW⟩:=ascent h y
   have ha:= C.S.a_pos j; have ha':= C.S.a_pos b; have hd:= C.S.strictAnti.antitone h
   have hz:= grid_for h w i; have hp := mapsR r (C.S.toDepth_odd h p) i; let a:=r.count.val; let s:Cover:= a • lift z+ lift i
   have hu:Lattice.wrap Y! s=y:= by unfold s; rw [← grid_wrap h (lift z) i,wrap_lift,show (Λ h p).assemble (z,i)=(Λ h p).embed z+ Lattice.wrap Y! (lift i) from rfl]; exact r.unpack_at y
   have η : lift z=w→lift y=s:= fun he=> by unfold s; rw [he]; exact hW
   by_cases he:lift y=s
   · left; apply Subtype.ext; funext u; unfold g g'; change f.val (o! z+ A j • (placeR r i+ (a:ℝ)⁻¹ • u))= f.val (o! y+ A b • u)
     apply congr_arg; rw [Schedule.place, grid_for h, Schedule.place,he]
   right; constructor
   · intro l hl x hx; unfold g feeR restricted; rw [Native.pulled,Native.pulled]; apply norm_le_zero_iff.mpr
     let t:=placeR r i+(a:ℝ)⁻¹ • x; have ht:t∈Native.box:= hp hx; suffices H:iteratedFDeriv ℝ l f.val (G! j (lift z)+ A j • t)=0 by unfold t a z at H; rw [Schedule.place, show iteratedFDeriv ℝ l f.val _=0 from H,smul_zero,smul_zero]
     by_contra h'; exfalso; apply he; refine reads_grid hu (lt_of_le_of_lt ?_ hR); have hv:=hf _ (support_iteratedFDeriv_subset l h'); have h₁:=grid_for h (lift z) i x; have h':G! j (lift z)+A j • t= G! b s+A b • x:=h₁; rw [h'] at hv; have hh: ‖A b • x‖≤ A b:=by rw [norm_smul,Real.norm_of_nonneg ha'.le]; exact mul_le_of_le_one_right ha'.le (Pert.Cellular.cells_bd hx)
     linarith [norm_le_insert (G! b s) (A b • x)] -- edit
   intro l hl x hx; unfold g' restricted; rw [Native.pulled]
   have h':G! b (lift y)+A b • x= G! j w+A j • (placeR r i+(a:ℝ)⁻¹ • x):=by nth_rw 1 [hW]; exact (hz x).symm
   suffices H: iteratedFDeriv ℝ l f.val (G! b (lift y)+ A b • x)=0 by rw [Schedule.place, show iteratedFDeriv ℝ l f.val _=0 from H,smul_zero,norm_zero]
   by_contra hv; apply he; apply η; refine reads_grid hw (lt_of_le_of_lt ?_ hR)
   let t:= placeR r i+(a:ℝ)⁻¹ • x; have hh:= hf _ (support_iteratedFDeriv_subset l hv); rw [h'] at hh
   have hu: ‖A j • t‖≤ A j:=by rw [norm_smul,Real.norm_of_nonneg ha.le]; exact mul_le_of_le_one_right ha.le (Pert.Cellular.cells_bd (hp hx))
   linarith [norm_le_insert (G! j w) (A j • t)] -- edit
-- MOST b roots never reach center test (including on full line jet)
lemma remote (h:j ≤ b)(f:Body){R:ℝ}(hf:∀ x∈tsupport f.val,‖x‖≤R)(hR: R+A b ≤ A j/4)(y:Site Y!)(hy:¬ separation y 0 ≤ (Λ h p).count.val/4)(k:ℕ) : Cap k (F! y f) 0:=by
    intro i hi x hx; unfold restricted; rw [Native.pulled]
    suffices H : iteratedFDeriv ℝ i f.val (o! y+A b • x)=0 by rw [H,smul_zero,norm_zero]
    by_contra he; apply hy; have ht:=hf _ (support_iteratedFDeriv_subset i he); have hb:=C.S.a_pos b;have hz: ‖A b • x‖≤ A b:=by rw [norm_smul,Real.norm_of_nonneg hb.le]; exact mul_le_of_le_one_right hb.le (Pert.Cellular.cells_bd hx)
    have hX := le_trans (norm_le_insert (o! y) (A b • x)) (le_trans (add_le_add ht hz) hR); have hσ:= (Ribbons.normC C b p y).1
    let r:=(Λ h p); have hv: 4*separation y 0 ≤ r.count.val := by
        exact_mod_cast (le_of_mul_le_mul_left (show A b*(4* (separation y 0:ℝ)) ≤ A b*r.count.val from by rw [C.S.embeds_scale]; linarith) hb)
    change _ ≤ r.count.val/4; omega
end YM.RG05Readout.Flatten
