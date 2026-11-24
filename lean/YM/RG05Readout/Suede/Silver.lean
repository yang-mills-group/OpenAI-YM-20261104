import YM.RG05Readout.Velvet.Ticket
import YM.RG05Readout.Planes.Wheel
import YM.OPE.Portfolio.Solemn
/-! Scalar slot normalized in same basis including WM.I. Mass by Gram uses this exact unit. Addresses after d=0 have only this slot. Tensor diagonal uses Native basis.Correction for its sole complex phase. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Suede
open Function MeasureTheory Set Filter Topology Pulse Native Address Many Lattice Wilson Extraction WithLp Nuclear Bay Cells Halls
open RG MergeProof Flatten PhysicalNext.Repeat Legato Dash Extraction.Lease Petals Push Push.RelayDifference Labels Source Extra.Histories
open MergeProof.Ribbons.ManyCopies.Cadet.Studio.ZeroDegree
open Planes Shadow Velvet
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{v i k b d m j p N:ℕ} (h:C.Makes)
-- pin layer letter via one integral jet. level diagnostics interpreted in native read. `line` val sets pairing convention. Unscaled.
def pip : Letter 0:=⟨⟨0,one_pos⟩, Classical.choice Planes.exists_letter⟩
lemma static0 (i:Letter 0) (y:E4) : (Native.line i).val y=(Native.line i).val 0:=by
   rcases i with ⟨i,x⟩; obtain rfl: i=(⟨0,one_pos⟩:Fin 1):=Fin.ext (by have := i.isLt; change i.val=0; omega); apply congr_arg ((BoltBasis 0 x).val); exact Subsingleton.elim _ _
lemma pitch_pos (i:Letter 0): (Native.line i).val 0≠0:=by
    intro h; have ht:Native.line i=0:=Subtype.ext (funext fun x=> Eq.trans (static0 i x) h); have hh:= headC i i; rw [ht,map_zero,if_pos rfl] at hh; exact zero_ne_one hh
lemma equal_letter (i:Letter 0): i=pip :=by
    let a:= (Native.line i).val 0 / (Native.line pip).val 0; have he : Native.line i= a • Native.line pip:=Subtype.ext (funext fun x=> (static0 i x).trans (show (Native.line i).val 0 = a*(Native.line pip).val x from (by unfold a; rw [static0 pip x,div_mul_cancel₀ _ (pitch_pos _)])))
    by_contra h; have ht:= headC i i; rw [he,map_smul,headC,if_neg h,smul_zero] at ht; exact zero_ne_one (ht.trans (if_pos rfl))
noncomputable def mother (C:Family G):Mark C 0:=⟨pip,0⟩
noncomputable abbrev firstC (C:Family G):Palette C 0:= ticket (mother C)
lemma mold (i:Mark C 0): i=mother C:=by
     rcases i with ⟨i,j⟩; obtain rfl:= equal_letter i; rw [show j=0 from one_at (F:=C.labels.level 0) j]; rfl
local notation "H"=> C.labels.level 0
local notation "F"=> firstC C
local notation "I"=> mother C
lemma first_chunk : firstC C=Address.chunk pip ((C.labels.level 0).e0):=rfl -- axis
local notation "R"=> C.path.rep N p
lemma prompt (f:Body): readJ pip 0 f * (Native.line pip).val 0=f.val 0:=by
   have he:= preciseAt 0 (i:=0) (f:=f) le_rfl; unfold Native.cut at he
   rw [Finset.sum_eq_single pip _ (fun h=>False.elim (h (Finset.mem_univ _)))] at he; rotate_left
   · intro i hi h; exact False.elim (h (equal_letter i))
   have hf:= congr_arg (fun x:Tensor.T E4 ℂ 0=> x (fun _=>0)) he; simpa only [iteratedFDeriv_zero_apply,SetLike.val_smul,Pi.smul_apply,smul_eq_mul] using hf
lemma val_first : Address.val (firstC C) (mother C)=1:=by unfold Address.val mother firstC ticket;change Address.chunk pip _ _ _=_; rw [chunk_self];exact Pi.single_eq_same ..
lemma letter_sum (x:Palette C 0) : val x (mother C) • firstC C=x:=by
    have h:=cardp x; rw [Finset.sum_eq_single (mother C) (fun i _ hi=> (hi (mold i)).elim) (fun h=>False.elim (h (Finset.mem_univ _)))] at h; exact h
include h
lemma corner (x:Site (C.side N p))(g:Body): entrance C 0 N p F x g=readJ pip 0 g • 1:=by
    unfold entrance; rw [Finset.sum_eq_single I (fun j _ h=> (h (mold j)).elim) (fun h=> False.elim (h (Finset.mem_univ _))),val_first,one_smul]; change _ • ((C.localSection 0).places ((H|>.scaled) _ ((C.labels.level 0).e0)) x)=_; apply congr_arg; rw [Frame.scaled_unit]; funext U; exact congr_fun ((h.sections 0).unit) _
omit h
variable {D:Address.Rail C}{B:ℕ→ℕ→ℝ}{V:Sight C 0 p}{U:Address.Emblems C 0}(hY:Spine D B h b p 0 N V U)(hw:Awake D B b 0)
local notation "M"=> liftVac C.path N p
local notation "T"=> Native.line pip
include hY hw h
lemma atSeed (ht:b≤N): pulseOut (V N F) T=M N:=by
   rw [hY.starts]; funext x
   change ((basisTop ..) F T).fst x= _; rw [Address.basis_agrees C 0 N p h (fun j hj=>(hw.post j hj).trans ht),corner h,headC,if_pos rfl,one_smul,Pi.one_apply,mul_one]; rfl
omit hw hY in
lemma acrossSeed (ht:m<N) (P:Tape G (C.side (m+1) p))(hz:pulseOut P T=M (m+1)) : journey C p m N 0 (pulseOut P) T=M m:=by
   let B:= Address.Bud C p m; have hx(i:B):Lattice.pull 1 (child C p m i)=(Lattice.pull (1:Signed) (child C p m i):Config G (C.side (m+1) p)→_):=rfl
   have hk(i:B): liftVac C.path N p (m+1) ∘ Lattice.pull 1 (child C p m i)=M (m+1):=funext fun U=> vac_pull C.path N p (m+1) h.wilson ht _ _ _
   have hf (t:E4)(r:ℝ): Native.pull t r T=T:=Subtype.ext (funext fun x=> Eq.trans (static0 pip _) (static0 pip x).symm)
   have hp:((Fintype.card B):ℂ)≠0:=by exact_mod_cast Fintype.card_ne_zero
   unfold journey Address.average; simp_rw [hf,hz,hk, blast_vac _ _ _ _ _ h.wilson ht,pow_zero,one_smul, Finset.sum_const,Finset.card_univ]; rw [← Nat.cast_smul_eq_nsmul («R»:=ℂ),smul_smul,inv_mul_cancel₀ hp,one_smul] -- argument parse
lemma measured_eq (ht:b ≤ m)(hz:m ≤ N): pulseOut (V m F) T=M m ∧ ∀ i:ℕ,m ≤ i→ i<N→ U i F=F:=by
    induction hz using Nat.decreasingInduction with
    | self=> exact ⟨atSeed h hY hw ht,fun i hp hi=>False.elim (by omega)⟩
    | of_succ i hi ih=>
       obtain ⟨h₁,h₂⟩:= ih (ht.trans i.le_succ); have hk:pulseOut (V i (U i F)) T=M i:= (travels h hY (hm:=hi) ht T F).trans (acrossSeed h hi _ h₁)
       let Q:= Extra.Histories.primary (0:Site (C.side i p)) (H|>.e0); let Y:= glyph (readJ pip 0) (invoice Q 0 (C.localSection 0) (R i)); have hx:= printed_one (o:= (0:Site (C.side i p))) («R»:=R i) pip (C:=C) Q (primary_format _) (primary_rem _ (Real.sqrt_pos.mpr (forcedPos C.path.levels i)))
       have hv :Trace.Physical.Germ.projection H C.params (R i).p.threshold 0 Q=(H|>.e0):=by
           have he: Trace.Physical.Germ.vector H C.params (R i).p.threshold (0:Site (C.side i p)) (0: Config G (C.side i p)→ℂ)=0:=by
               unfold Trace.Physical.Germ.vector Trace.Physical.Germ.label; split
               next h=> rw [show h.choose=0 from Next.Foundations.JetTest.unique h.choose_spec ((Next.Foundations.jetTest_zero_iff ..).mpr (fun i=>⟨contDiffAt_const,fun k _=> by simp⟩)),map_zero,map_zero]
               next=> simp
           change _+∑' u:ℕ,Trace.Physical.Germ.vector _ _ _ _ (Q.regular u)= _; unfold Q; simp only [Extra.Histories.primary, Pi.zero_apply]; simp only [he,tsum_zero,add_zero] -- issue
       have hπ:pulseOut Y T=M i:=by unfold Y pulseOut; rw [glyph_apply,headC,if_pos rfl,one_smul]; exact unit_density ..
       obtain ⟨A,hA⟩:=(hY.legal i ht hi.le).capacity0 (U i F); obtain ⟨r,A',s,c,D,V,Z,hZ⟩:= (hw.toll p i N ht hi).author
       rw [show Trace.Physical.Germ.projection (C.labels.level (kept pip)) C.params (R i).p.threshold 0 Q=(C.labels.level (kept pip)).e0 from hv] at hx
       have hG:U i F=F:= by rw [first_chunk]; exact hA.survives hx (fun j=>⟨_,Z.cursor.sense _ (Nat.sub_le ..)⟩) (fun i'=>by rw [equal_letter i']; exact EventuallyEq.of_eq (hk.trans hπ.symm))
       refine ⟨hG ▸ hk,fun j hx hh=>?_⟩; by_cases h:i=j; exact h ▸ hG; exact h₂ _ (by omega) hh
end YM.RG05Readout.Suede
