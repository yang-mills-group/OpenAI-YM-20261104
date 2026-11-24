import YM.RGLocalTaylor.Mayer.Moment

/-!
# One actual tower through all regulator horizons on one construction

Read the retained thermal log coefficients from the same perturbative recipe
independent of M. Off-mask values of all orders are needed for later path
movement & measurability. This is NOT a statement of compatibility across
changing histories or cash inputs. For the full density approx and Cauchy error
price at a cutoff always include the last slot of `issue` after specifying M.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
namespace Mayer
variable {p select : Molecule S} {m M M' : ℕ} (u : Decors select M) (f' : Head S → Insert T)

lemma cast_payload (v : Decors select M') (he: ∀ i,(u i).val = (v i).val) (hu : decorOrder u ≤ M) (hv:decorOrder v ≤ M') :
    payload H p f' u=payload H p f' v:= by
  funext i; unfold payload; split
  next hi=>
    let I:↥select:=⟨i,hi⟩
    change kernelQuote H (own p) (u I) i=_
    change _ = kernelQuote H (own p) (v I) i
    rw [show u I = (⟨(u I).val,decorOrder_lt hu I⟩:Fin M).castSucc from rfl, show v I = (⟨(v I).val,decorOrder_lt hv I⟩:Fin M').castSucc from rfl]; unfold kernelQuote; simp_rw [index_cast]; exact congr_arg₂ _ (congr_arg atOrder (he I)) rfl -- args?
  rfl

lemma fixed (p select : Molecule S) (h:m≤M) (h':m≤M') (f' : Head S → Insert T) : coefficient p select H f' χ M m=coefficient p select H f' χ M' m:= by
  funext V
  unfold coefficient
  let S M:= univ.filter (fun g:Decors select M=> decorOrder g=m)
  let u' {L M:ℕ} (h:m ≤ M) (u:Decors select L) (hk:u∈S L) i : Fin (M+1) := ⟨(u i).val,(Finset.single_le_sum (s:=univ) (f:=fun i:↥select=>(u i).val+1) (fun _ _=> Nat.zero_le _) (mem_univ i)).trans (((mem_filter.mp hk).2.le.trans h).trans (Nat.le_add_right M 1))⟩
  apply Finset.sum_bij (u' h')
  · intro i hi; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩
  · intro a₁ ha b hb hh; exact funext fun i=> Fin.ext (congr_arg (@Fin.val (M'+1)) (congr_fun hh i))
  · intro i hi; exact ⟨u' h i hi,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩,rfl⟩
  intro i hi; unfold tagged; rw [cast_payload (H:=H) (p:=p) i f' (u' h' i hi) (fun _=>rfl) ((mem_filter.mp hi).2.le.trans h) ((mem_filter.mp hi).2.le.trans h')]

lemma cast_issue {p : H.ThinP} (i:Fin (M+1)) (i':Fin (M'+1)) (h:i.val=i'.val) : issue H χ M p i.castSucc=issue H χ M' p i'.castSucc:= by
  unfold issue; simp only [Fin.val_castSucc]; rw [if_neg (show i.val≠ M+1 from i.isLt.ne),if_neg (show i'.val≠M'+1 from i'.isLt.ne),atLeaf,atLeaf]; split
  next=> rw [h]; exact fixed _ _ (h ▸ Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ i'.isLt) _
  rfl

end Mayer
end YM.RGLocalTaylor
