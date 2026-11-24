import YM.RG05Readout.Petals.Wave
import YM.RG05Readout.Bay.Sachet
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Petals
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "L"=> C.path.levels
local notation "χ"=> C.path.levels.clock.J
local notation "λ₀"=> C.S.toDepth
local notation "Α"=> C.S.a
local notation "R0"=> C.path.rep N p
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

local notation "L!"=> Lattice.wrap
variable {f: Extraction.Order}
set_option quotPrecheck false
/-! Prove sufficient for the **upper** calibration and for cost through lower
  horizons.The Forward displacement sign in RawProtected keeps WardBin priced
  on same compact family. Not using thresholds of coarser renewal families. -/
-- conjunction for providing.Capacity lower e.
structure Abides (C:Family G)(f : Extraction.Order)(P:Trial C)(d:ℕ) : Prop where
    header : RawProtected C f P d
    native : Stencilled f P
    root (N p:ℕ)(z): Continuous (P N p z)
section
variable {X Y:Trial C} (ht:Abides C f X d)
include ht
open Next.Foundations
lemma Abides.scales (z:Cutoffs→ℂ)(hz:Slow C f z) : Abides C f (fun N p x=> z (N,p) • X N p x) d:=by
    obtain ⟨s,hs,c,b,hc,hb,hX⟩:=ht.header; obtain ⟨S,hS⟩:=ht.native
    refine ⟨⟨s,hs,_,_, hz.norm.mul hc,hz.norm.mul hb,hX.mono (fun j hj=>hj.mono fun i hi x=> ?_)⟩,⟨S,hS.mono fun i hi=> hi.smul _⟩,fun _ _ x=> (ht.root _ _ x).const_smul _⟩
    obtain ⟨hk,hK,ha,hA⟩:= hi x; unfold unpriced; rw [smul_comm]; exact ⟨regular_smul _ hk,bound_smul _ hK, mul_nonneg (norm_nonneg _) ha,fun U=> (norm_smul_le (z (f.mesh i,f.per j)) (unpriced C X d _ _ x U)).trans (mul_le_mul_of_nonneg_left (hA _) (norm_nonneg _))⟩
lemma Abides.add (hr:Abides C f Y d) : Abides C f (X+Y) d:=by
    obtain ⟨s,hs,c,u,hc,hu,hX⟩:=ht.header; obtain ⟨t,hT,g,b,hg,hb,hY⟩:=hr.header
    obtain ⟨S,hS⟩:=ht.native; obtain ⟨V,hV⟩:=hr.native
    refine ⟨⟨s∪t,Finset.mem_union_left _ hs,_,_,hc.add hg,hu.add hb,(hX.and hY).mono (fun j hj=> (hj.1.and hj.2).mono fun i hi x=> ?_)⟩,⟨S∪V,(hS.and hV).mono fun i hi=> hi.1.add hi.2⟩,fun i j x=>(ht.root i j x).add (hr.root i j x)⟩
    obtain ⟨ha,hA,hq,hQ⟩:= hi.1 x; obtain ⟨he,hE,hL,hL'⟩:=hi.2 x
    let D := regional (s∪t) x; have hv:regional s x⊆D:= Finset.image_subset_image Finset.subset_union_left; have hv':regional t x⊆D:= Finset.image_subset_image Finset.subset_union_right
    simp only [unpriced,Pi.add_apply,smul_add]; exact ⟨regular_add (regular_larger ha hv) (regular_larger he hv'), bound_add (regular_larger ha hv) (regular_larger he hv') (bound_larger hA hv) (bound_larger hE hv'), add_nonneg hq hL,fun U=> (norm_add_le (unpriced C X d _ _ x U) (unpriced C Y d _ _ x U)).trans (add_le_add (hQ _) (hL' _))⟩
omit ht
include h
-- avoid assuming core locality in every period except through nominated primary.
lemma generic (hG:G.Simple)(x:Rowe C d)(hp:dollar C f x): Abides C f (Bid.upper C x) d:=⟨RawProtected.upper h hG x hp,Stencilled.upper h x,fun _ _ _=>C.continuousO ..⟩
lemma Adzero (hG:G.Simple): Abides C f 0 d:=by
    let z:Rowe C d:= fun _=>0; have hz:Bid.upper C z=0:=funext fun i=>funext fun j=>funext fun x=> (C.linearO i j d x|>.mk' _).map_zero
    exact hz ▸ generic h hG z (Work.D01.answer C h d f z ⟨0,Eventually.of_forall (fun i=>Eventually.of_forall fun j=> norm_zero.le)⟩)
lemma Adsum {V:Type*} (hG:G.Simple)(s:Finset V)(F:V→Trial C)(hS:∀ i∈s, Abides C f (F i) d) : Abides C f (∑ i∈s,F i) d:=by
    induction s using Finset.induction_on with|empty=>rw [Finset.sum_empty];exact Adzero h hG|insert i s hi ih=>rw [Finset.sum_insert hi]; exact (hS i (Finset.mem_insert_self ..)).add (ih fun j hj=> hS j (Finset.mem_insert_of_mem hj))
omit h
include ht
lemma Abides.step (a:Axis) (hp:shiftCosts C f) : Abides C f (fun N p x=> X N p (x+Lattice.step a)) d:=by
    obtain ⟨s,hs,c,b,hc,hb,H⟩:=ht.header; let D:= s.image (fun x=>x+Lattice.step a)∪s; obtain ⟨V,hV⟩:=ht.native
    refine ⟨⟨D,Finset.mem_union_right _ hs,_,_,(show Slow C f (fun i=> jump (C.path.levels.budget i.1)) from hp).mul hc,hb,H.mono (fun j hj=>hj.mono fun i hi x=> ?_)⟩,⟨V.image (fun x=>x+Lattice.step a), hV.mono (fun i hi=> hi.step a)⟩,fun N p x=> ht.root N p _⟩
    obtain ⟨hx,hX,ha,hA⟩:= hi (x+Lattice.step a)
    have hq:regional s (x+Lattice.step a)⊆regional D x:=by
        intro k hk; obtain ⟨y,hy,rfl⟩:= Finset.mem_image.mp hk; exact Finset.mem_image.mpr ⟨_,Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy), by rw [map_add,wrap_step]; abel⟩
    have he: separation (x + Lattice.step a) x ≤ 1 := by rw [separation,add_comm,add_sub_cancel_right]; exact pdist_step _
    exact ⟨regular_larger hx hq,bound_larger (dir_shift _ _ _ _ _ he hX) hq, ha,hA⟩
lemma Abides.native_steps (a: Slots k) (hp:shiftCosts C f) : Abides C f (fun N p x=> X N p (x + Lattice.wrap _ (backward a))) d:=by
    have hw(g:Finset Axis):Abides C f (fun N p x=> X N p (x+∑ i∈g, (a i).val • Lattice.step i)) d:=by
       induction g using Finset.induction_on with
       | empty=> simpa only [Finset.sum_empty,add_zero] using ht -- ht output
       | insert i s hi ih=>
          have he(n:ℕ):Abides C f (fun N p x=>X N p (x+(n • Lattice.step i+∑ i∈s,(a i).val • Lattice.step i))) d:=by
             induction n with | zero=>simpa using ih|succ n ih'=>
                have h:=ih'.step i hp; convert h using 1; funext N p x; apply congr_arg; rw [succ_nsmul]; abel
          simp_rw [Finset.sum_insert hi]; exact he (a i).val
    have hh {n:Side}: Lattice.wrap n (backward a)=∑ i:Axis,(a i).val • Lattice.step i:=by
       funext i; rw [Finset.sum_apply,Finset.sum_eq_single i]; rotate_left
       · intro j _ hj; simp [Lattice.step, Ne.symm hj,Pi.single_eq_of_ne]
       · simp
       simp [Lattice.wrap,backward,Per]
    simp_rw [hh]; exact hw _
end
section
variable (X: Cutoffs → Palette C d) {e:ℕ}
local notation "Σ₁"=> Address.Mark C d
variable (j:Address.Mark C d)
local notation "q'"=> C.path.rep N p N
local notation "H₀"=> C.path.levels
local notation "G₀"=> C.labels.level
local notation "Z"=> C.S.a
abbrev rise (M:Palette C d)(j:Address.Mark C d)(N p:ℕ):= (C.factory (kept j.1) N p).terminal (val M j • Size.axis (C.labels.level (kept j.1)) j.2)
lemma pulses_key (H:C.Makes)(z:Site (C.side N p))(M:Palette C d): key C N p d M j z=(Z N:ℂ)^(kept j.1) • C.O N p (rise M j N p) z:=by
    let v:= rise M j N p; rw [show C.O N p (rise M j N p) z=stepUp (1,false) z (C.O N p v 0) from unorient (local_primary H v).translates z, show (Z N:ℂ)^_ • stepUp _ z _=stepUp (1,false) z (Push.RelayDifference.weight C (kept j.1) N • C.O N p v 0) from (Records.rot_scalar (1,false) z (Push.RelayDifference.weight C (kept j.1) N) (C.O N p v 0)).symm]; rw [Push.RelayDifference.charged];
    unfold v rise; rw [LinearEquiv.symm_apply_apply];
    have hh:=H.wilson.represents N p N le_rfl
    rw [show (C.localSection _).places _ _=Local.presented (C.localSection (kept j.1)) 0 (C.path.levels.budget N).threshold (val M j • Size.axis (C.labels.level _) j.2) from rfl,map_smul,Records.rot_scalar]
    unfold Pulse.key; rw [hh.vac]; rfl

noncomputable def magnify (C:Family G)(m N d:ℕ):ℂ:=((C.S.a m:ℂ)/(C.S.a N:ℂ))^d
noncomputable def pitch (m:ℕ): Trial C:=fun N p x => magnify C m N d • key C N p d (X (N,p)) j x
include h
local notation "Z!"=> (Z N:ℂ)
lemma horn (hG:G.Simple)(he:e≤d) (hw:Slow C f (fun i:Cutoffs=> ((C.S.a i.1:ℂ)^(d-e))⁻¹ • X i)): Abides C f (pitch X j m) e:=by
    let Y (i:Cutoffs): Palette C d:= ((C.S.a i.1:ℂ)^(d-e))⁻¹ • X i; let w:Rowe C (kept j.1):= fun i=>rise (Y i) j i.1 i.2
    have hS(v:Cutoffs): ‖val (Y v) j‖≤‖Y v‖:= (norm_le_pi_norm ((Y v) j.fst) _).trans (norm_le_pi_norm (Y v) _)
    have hb : dollar C f w:= (dollar_slow _).2 (by
       let L':= (C.labels.level (kept j.1)); let a:=Size.axis L' j.snd; have h: Slow C f (fun i=> val (Y i) j • a):= (hw.reduce (v:=fun i=> val (Y i) j) (Eventually.of_forall hS)).smul (Slow.const a); unfold w rise; simpa only [LinearEquiv.symm_apply_apply] using h)
    obtain ⟨hp,hT,hA⟩:= generic h hG w hb; let A':= (Z m:ℂ)^d; let P(N:ℕ):=A'* ((C.S.a N:ℂ)^e)⁻¹*(C.S.a N:ℂ)^(kept j.1);
    have hv : pitch X j m=fun N p x=> P N • (Bid.upper C w N p x):=by
       funext N p x; unfold pitch P; let R:=(X (N,p)); let r:=rise R j N p; let c := ((C.S.a N:ℂ)^(d-e))⁻¹
       have hw':w (N,p)= c • r:= by unfold w rise; rw [← map_smul]; exact congr_arg _ (mul_smul ..)
       rw [pulses_key _ h]; unfold Bid.upper; rw [hw', (C.linearO ..).map_smul,smul_smul,smul_smul]; congr 1; change magnify C m N d * _ = _*c; unfold magnify c; have h0:(Z N:ℂ)≠0:= Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne'; dsimp only [A']; rw [div_pow]; have heq:(C.S.a N:ℂ)^d=(C.S.a N:ℂ)^e*(C.S.a N:ℂ)^(d-e):=by rw [←pow_add,Nat.add_sub_of_le he]
       field_simp; rw [heq]; ring
    rw [hv]; obtain ⟨V,hV⟩:=hT; refine ⟨?_,⟨V,hV.mono fun i hi=> hi.smul _⟩,fun N p x=>(hA N p x).const_smul _⟩
    have hz:RawProtected C f (fun N p x=> A' • (Bid.upper C w N p x)) (kept j.1):= ((Abides.scales (⟨hp,⟨_,hV⟩,hA⟩:Abides C f (Bid.upper C w) (kept j.1)) (fun _=>A') (Slow.const _))).header
    have hx (N p:ℕ)(x): unpriced C (fun N p x=> P N • (Bid.upper C w N p x)) e N p x=unpriced C (fun N p x=> A' • (Bid.upper C w N p x)) (kept j.1) N p x:=by
       unfold unpriced; rw [smul_smul,smul_smul]; congr 1; unfold Push.RelayDifference.weight P; have he: (Z N:ℂ)≠0:= Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne'; field_simp
    simpa only [RawProtected,hx] using hz
end
end YM.RG05Readout.Petals
