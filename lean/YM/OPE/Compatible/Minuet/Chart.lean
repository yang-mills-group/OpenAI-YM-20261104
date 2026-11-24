import YM.OPE.Compatible.Minuet.Scribble
/-! # Primacy geometry along same coarse chart. No wrap comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset
open Next.Rank.Thirst
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : Rep G f}
    {p : BudgetPoint} {m n: ℕ} {W a r t σ E Λ μ x κ C w ε D b: ℝ} {Ñ:ChartRatio G}
lemma upload (l : Ratio c f) (x y : Site c) : separation (l.embed x) (l.embed y) ≤ l.count.val* separation x y:=by
  unfold separation; rw [← l.root_embed,← l.root_embed,← map_sub,l.root_embed]
  refine Finset.sup_le ?_; intro i hi
  rw [l.lift_embed]; simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ (component_le _ _)
lemma haloY (n m:ℕ)(X:Support f): halo n (halo m X) ⊆ halo (n+m) X:=by
   intro x hx; obtain ⟨p,hp,he⟩ := halo_spec.mp hx;obtain ⟨z,hz,h⟩:=halo_spec.mp hp; exact halo_spec.mpr ⟨z,hz,(separation_triangle z p x).trans (by omega)⟩
abbrev roomB (p:Site f)(d:ℕ):Support f:=halo d {p}
lemma pacing {P:Support f}{o:Site f}(he:P⊆roomB o n){x : Site f}(hx:x∈P): separation o x ≤ n:=by simpa [halo_spec] using he hx
lemma pulseR (p:Site f)(d:ℕ):coverNumber 1 (roomB p d) ≤ (d+d+1)^4:=by
    apply le_trans (b:=(roomB p d).card) _ (by simpa using Corona.halo_size {p} d)
    refine list_cost _ ⟨halo_subset .., ship_halo _ (fun i hi j hj=> ?_)⟩
    apply Relation.ReflTransGen.mono (fun a b hh=> ?_) _ _ ((ship_halo  d (D:={p}) ?_) i hi j hj)
    · intro i hi j hj; rw [mem_singleton.mp hi, mem_singleton.mp hj]
    exact ⟨hh.1,hh.2.1,hh.2.2.trans (by omega)⟩
variable (F:Forest S.ratio)
def seatB (P:Support f):Seats F := Finset.univ.filter fun i:F.Free=> i.val.1∈P
def rope (T : Patch)(d:ℕ):= 16+d+(4*T.L.val+1)
lemma gripY (I:Seats F) {p:Site f}(hh:I⊆seatB F (roomB p m)): FoldsGrip F I (roomB p (rope S.patch m)):=by
   have hx : chairFoot (chairMap F I)⊆ roomB p m:=by
      intro i hi; obtain ⟨j,hj,rfl⟩:= mem_image.mp hi;obtain ⟨k,hk,rfl⟩:=mem_image.mp hj; exact (mem_filter.mp (hh hk)).2
   refine ⟨⟨p,halo_subset _ _ (mem_singleton_self _)⟩,?_,?_⟩
   · intro i hi; apply (walksIn F i).trans; intro z hz; obtain ⟨y,hy,hz⟩:=halo_spec.mp hz
     have hu : i.1∈ roomB p m:= hx (mem_image_of_mem _ hi)
     rw [mem_singleton.mp hy] at hz; exact halo_spec.mpr ⟨_, Finset.mem_singleton_self _,(separation_triangle p i.1 z).trans (by have hv:=pacing (show roomB p m ⊆ roomB p m from Finset.Subset.refl _) hu; unfold rope; omega)⟩ -- p implicit name P
   dsimp only
   refine (Next.Scheduling.flag_layer _).trans (?_)
   apply (halo_mono (a:=8) (b:=8) le_rfl ((Next.Scheduling.flag_layer _).trans (halo_mono le_rfl hx))).trans
   apply ((halo_mono (b:=8) le_rfl (haloY (f:=f) 8 m {p})).trans (haloY ..)).trans; exact halo_mono (by unfold rope; omega) le_rfl
def pArc (P:Patch)(m:ℕ):= m+P.L.val+predReach P+1 -- parent span m via bound
lemma archway (p:Site c)(m:ℕ){x:Site f}(hx:x∈roomB (S.ratio.embed p) m):separation p (S.ratio.parent x) ≤ m +S.patch.L.val:=by
    have hp:= Corona.foreshorten S.ratio (S.ratio.embed p) x; rw [S.ratio.embed_parent] at hp; apply le_trans _ (le_trans hp (Nat.add_le_add_right ?_ _)) -- wrong add
    · exact Nat.le_mul_of_pos_left _ S.patch.L.property
    exact pacing (show roomB _ m ⊆ roomB _ m from Finset.Subset.refl _) hx
def circuitY (P:Patch)(B d:ℕ):= ySpan B+ rope P d
-- X bound halo O at same fine p. O radial. 
def o_cover (P:Patch)(d B n:ℕ):= 8+circuitY P B d+P.L.val* (pArc P d + max n (predReach P+1))+P.L.val
lemma mainRing (o:Site c) (d B n:ℕ)(I:Seats F)(hp:I ⊆ seatB F (roomB (S.ratio.embed o) d)) :
    let p:= S.ratio.embed o; let f:= o_cover S.patch d B n; let X:= roomB p (rope S.patch f); let Y:=roomB p (circuitY S.patch B d); let Q:=pArc S.patch d
    Primacy F I (seatB F (roomB p f)) Y X (roomB p (rope S.patch d)) (roomB o Q) B n:=by
      intro p f X Y Q; refine ⟨hp.trans (?_),gripY F I hp,haloY ..,gripY F _ (Finset.Subset.refl _),?_,?_,?_⟩ -- edit
      · intro i hi; exact Finset.mem_filter.mpr ⟨mem_univ _,halo_mono (X:={p}) (a:=d) (b:=f) (by unfold f o_cover circuitY rope; omega) le_rfl (mem_filter.mp hi).2⟩
      · intro i hi; apply Finset.mem_filter.mpr; exact ⟨mem_univ _,halo_mono (show 8+circuitY S.patch B d ≤ f by unfold f o_cover;omega) le_rfl (haloY 8 _ {p} (Next.Scheduling.flag_layer _ hi))⟩
      · intro i hi; obtain ⟨z,hz,h⟩:=halo_spec.mp hi; let x:=i.val.1
        have hx : separation o (S.ratio.parent x) ≤ Q + max n (predReach S.patch+1) :=(separation_triangle o z _).trans (Nat.add_le_add (pacing (show roomB _ Q⊆ _ from Finset.Subset.refl _) hz) h)
        have hy := (upload S.ratio o (S.ratio.parent x)).trans (Nat.mul_le_mul_left _ hx)
        have hu := Corona.near S.ratio x
        change 2*separation x _≤ S.patch.L.val at hu
        refine Finset.mem_filter.mpr ⟨mem_univ _,halo_spec.mpr ⟨_,mem_singleton_self _,(separation_triangle p (S.ratio.embed (S.ratio.parent x)) x).trans ?_⟩⟩
        rw [separation_comm _ x]; unfold f o_cover; change separation p _ ≤ S.patch.L.val*_ at hy; unfold Q at hy; omega
      intro i hi hf; obtain ⟨z,hz,h⟩:= halo_spec.mp hf; apply mem_compl.mp hz; have hh:=archway (S:=S) o d (show i.val.1∈roomB p d from (mem_filter.mp (hp hi)).2)
      exact halo_spec.mpr ⟨o,mem_singleton_self _, (separation_triangle o (S.ratio.parent i.val.1) z).trans (by rw [separation_comm z] at h; unfold Q pArc;omega)⟩
end YM.PhysicalNext.Repeat.Aroma
