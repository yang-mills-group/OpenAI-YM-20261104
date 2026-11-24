import YM.GradedFar.Moving.Timber

/-!
# Fixed profile comparison with `G^P`, same shape as the actual clock pose

Let's state only the no-derivative version of the compact comparison here. Later supply it
from PoseFit's C5 inputs. One may also want the following unnormalized & normalized price transfer
methods for composite terms.
-/
namespace YM.FVA2.GradedFar.Moving
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury Facets Growth
open MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d e : ℕ} {I J : Type} {p : ℕ} (T : Filter I) (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "ν"=> Teller.logNu 1
local notation "ψ"=> GroupS.ψ N.criterion M ν
variable (r z : I→ℝ) (hr : Tendsto r T τ) (hz : ∀ᶠ i in T,z i∈Growth.Small) {simple : G.Simple}
    {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
include H hr
variable {F : Pose.Plans G d} (θ : ℝ→ℝ)
def Beginning (θ : ℝ→ℝ) (d : ℕ) (F : Pose.Plans G d) : Prop := ∀ (n : ℕ) (q : ℕ) (K : Set (Points n)), IsCompact K→ K⊆conf n →
    ∀ u : Tags G d n, Pose.Terms τ (fun r=> g r^(q+1)) (fun r (x:↥K)=> F r n x.val u - crop q (θ r) (Pose.line N x.val u))

variable {K : Set (Points n)} (x : I→Points n) (hK : IsCompact K) (hx : K⊆conf n) (he : ∀ᶠ i in T, x i∈K)
include hK hx he

lemma beauty (u : Tags G d n) : Till T (fun i=> tells (Pose.line N (x i) u)) (g ∘ r) p := by
    intro j hj; obtain ⟨C,h⟩:= hK.exists_bound_of_continuousOn (f:=fun i=> tells (Pose.line N i u) j)
      (by simp_rw [Pose.line,tells,coeff_mk]; exact ((Pose.birth N M H d).1 _ j u).mono hx)
    exact budget T ((he.and (hr.eventually (positive_g simple))).mono fun i hi=> h _ hi.1)

variable (h : Beginning N θ d F)
include h
lemma born (u : Tags G d n) : Pays T (fun i=> F (r i) n (x i) u) (fun i=> tells (Pose.line N (x i) u)) (g ∘ r) p (fun i=>(θ (r i):ℂ)) := by
    refine ⟨beauty T N M r hr H x hK hx he u,?_⟩
    obtain ⟨C,hC,h⟩:= (h n p K hK hx u).price; apply IsBigO.of_bound C
    filter_upwards [hr.eventually h,he] with i hi he
    simpa only [crop_by, Function.comp_apply] using hi ⟨x i,he⟩
-- forma equivalence
include hz
private lemma enlarged : ∃ S' : Set (Points n), IsCompact S' ∧ S'⊆conf n ∧
    ∀ᶠ i in T, exp (z i) • x i ∈ S' := by
    cases H
    obtain ⟨_, _, hθ⟩ := (h n 0 K hK hx (fun _ => 0)).price
    let X : ℝ × Points n → Points n:= fun p=> exp p.1 • p.2
    refine ⟨X '' (Growth.Small ×ˢ K), (isCompact_Icc.prod hK).image
      ((Real.continuous_exp.comp continuous_fst).smul continuous_snd), ?_, ((hz.and he).and (hr.eventually hθ)).mono fun i hi=> mem_image_of_mem X (show (z i,x i)∈_ from hi.1)⟩
    rintro _ ⟨⟨i,j⟩,⟨hi,hj⟩,rfl⟩; have hh := Extent.placed (-i) j (hx hj); rw [neg_neg] at hh; exact hh

variable (ht : Tendsto (fun r=> θ r/gYM G r) τ (𝓝 1))
def ray (s r : ℝ) (p d : ℕ) := Continuation.atColumn (train N M d s) p (θ r)
include ht
lemma bought (u : Tags G d n) :
    Pays T (fun i=> F (r i) n (exp (z i) • x i) (ray N M θ (z i) (r i) p d ∘ u))
      (fun i=> tells ((Pose.line N (x i) u).subst (ψ (-z i)))) (g ∘ r) p (fun i=>(θ (r i):ℂ)) := by
    obtain ⟨S',hc,hp,hf⟩:= enlarged T N M (F:=F) r z hr hz H θ x hK hx he h
    have hv := titles T (g ∘ r) _ ((shrink simple).comp hr) (measuring T N M r hr H θ ht) _
      (A:=fun i=> fxt (Pose.Bbook N d) (exp (z i) • x i)) _ u (F:=fun i=> F (r i) n (exp (z i) • x i))
      (shine T N M r z hr hz H θ ht p d) (fun v=> born T N M r hr H θ _ hc hp hf h v)
    refine ⟨?_, ?_⟩
    · simp_rw [composition_tells _ _ (tendsK N M H _|>.start)]; exact shifted T (psi_lin T N M r z hz H) (beauty T N M r hr H x hK hx he u)
    apply hv.2.congr' _ (EventuallyEq.refl ..)
    filter_upwards [he.mono fun i h=> hx h] with i hi
    let a : Stage n := ⟨x i,hi⟩; let c:= z i
    unfold ray
    have hl : exp (z i) • x i = (Facets.posing (-c) a).val:= by unfold Facets.posing c; dsimp; rw [neg_neg]
    rw [hl,Jury.exactC, train_exact N M H, shop, Reg.Point.moves _ _ ((tendsK N M H c).start)]
    rw [show Pose.line N (x i) u=shop (Pose.Bbook N d n a) u by unfold Pose.line shop Reg.Point.story; rw [show x i=a.val from rfl,Jury.exactC]]

def new_clock (s r : ℝ) (p : ℕ) := (bend N M s p (θ r:ℂ)).re
omit hr hz h ht hK hx he in
lemma bend_real (s : ℝ) (t : ℝ) (p : ℕ) : ((bend N M s p t).re:ℂ)=bend N M s p t := by
    let A:=ψ (-s)
    have he := (tendsK N M H s).real
    have hh j : starRingEnd ℂ (coeff j A)=coeff j A := (coeff_map _ _ _).symm.trans (congrArg (coeff j) he)
    apply Complex.conj_eq_iff_re.mp
    unfold bend blend tells; simp_rw [map_sum,smul_eq_mul,map_mul,map_pow,Complex.conj_ofReal]; apply Finset.sum_congr rfl; intro i hi; rw [show (ψ (-s))=A from rfl,hh]

/-- Uniform O(g^{p+1}) on trial in the compact ratio, now on the forecast in
`Ψ_{η}(t)` cropped provisionally. -/
theorem hom_trial (u : Tags G d n) :
    Buys T (fun i=> F (r i) n (exp (z i) • x i) (ray N M θ (z i) (r i) p d ∘ u) -
      crop p (new_clock N M θ (z i) (r i) p) (Pose.line N (x i) u)) (g ∘ r) (p+1) := by
    have hV:= recrop_substitution T (measuring T N M r hr H θ ht) ((shrink simple).comp hr) (psi_lin T N M r z hz H) (fun i=>(tendsK N M H _).start) (beauty T N M r hr H x hK hx he u)
      (p:=p)
    refine ((bought (T:=T) N M r z hr hz H θ x hK hx he h ht u).2.sub hV).congr_left (fun i=>?_)
    dsimp only; rw [composition_tells _ _ (tendsK N M H _|>.start),crop_by,new_clock,bend_real N M H]; unfold bend ray; abel
end
end YM.FVA2.GradedFar.Moving
