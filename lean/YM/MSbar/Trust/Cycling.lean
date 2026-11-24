import YM.MSbar.Trust.Chance
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{r:Ratio c f}{U W:Config G f}{V:Config G c}{R:Rep G f}{σ C T a v x y δ w:ℝ}
open Finset
open YM.MSbar.Bulk SectorNext.Vacuum
open Tree
variable (F: Forest S.ratio) (s:F.Slice G)
local notation "N" => Config G f
local notation "σθ"=> Site f
local notation "Wθ"=>F.foldAt
def pedal (U: N) (p:Edge (Site f)): G.El:=(Wθ U p.1)⁻¹* F.drape s p * Wθ U p.1 * U p
local notation "Q"=> pedal F s
lemma pedaling : Continuous Q := by apply continuous_pi; intro p; unfold pedal; fun_prop
lemma centered (B: N): F.foldAt (Q B)=F.foldAt B :=F.names _ _ (fun p hp=>by unfold pedal; rw [show F.drape s p=1 from F.on_tree _ ⟨p,hp⟩]; group)
lemma stationary (U:N)(p:F.Free) : canoe (S:=S) F (Q U) p.val=s p*canoe (S:=S) F U p.val:=by unfold canoe; rw [centered]; unfold Lattice.gauge pedal; rw [F.off_tree]; group
lemma dodge (v:σθ→G.El)(B:N) (ht:∀ i,v (S.ratio.embed i)=1) : Q (gauge v B)=gauge v (Q B):=by
    funext i; unfold Lattice.gauge pedal
    have hf(w) : Wθ (gauge v B) w= Wθ B w*(v w)⁻¹:=by unfold Forest.foldAt; rw [travel_gauge,F.hike_root,ht]; group
    unfold Lattice.gauge at hf; dsimp only; rw [hf i.1]; group
lemma anchored (u:F.Slice G) (p: Site f): F.foldAt (F.drape u) p=1:=by
    rw [F.names _ 1 (fun i hi=>F.on_tree u ⟨_,hi⟩)]; unfold Forest.foldAt; have h(w : Walk)(y: Site f): travel (1:Config G f) y w=1:=by induction w generalizing y with
                                                                              | nil=>rfl
                                                                              | cons d w ih=> simp [travel, Step.read, ih]
    rw [h, inv_one]
lemma displayed (u: F.Slice G) : Q (F.drape u)= F.drape (s*u):=by
    funext i
    unfold pedal; rw [anchored]; simp only [inv_one,one_mul,mul_one]; by_cases he:i∈ F.trunks
    · rw [show F.drape u i=1 from F.on_tree _ ⟨i,he⟩,show F.drape s i=1 from F.on_tree _ ⟨i,he⟩]; exact (one_mul _).trans (F.on_tree (s*u) ⟨i,he⟩).symm
    let j:F.Free:=⟨i,he⟩; change F.drape s j.val* F.drape u j.val=_; rw [F.off_tree, F.off_tree,show F.drape (s*u) i=(s*u) j from F.off_tree (s*u) j]; rfl
-- only gauge relative. forest independence optional.
def Sweet (S:StepData c f)(A:Set (Config G f)):=∀ t:σθ→ G.El,(∀ i,t (S.ratio.embed i)=1)→∀ U: Config G f,U∈A ↔ gauge t U∈A
variable (hd : S.patch.Branches S.kernel G) (h:Admitted V R S σ C δ T w)
-- integrals orbit on tree slice.Any nonnegative costs purchased externally.
lemma tribute (g:N→ℝ)(hg:S.Inner g)(hv:Envelope g) : (∫ U,g (Q U)∂prior G f)=(∫ U,g U ∂prior G f):=by
    have hi(k : Edge (Site f)):True:= trivial
    have h:Envelope (g∘Q):=by obtain ⟨b,hb⟩:=hv.cost; exact ⟨hv.meas.comp (pedaling F s).measurable,b,fun i=> hb _⟩
    rw [F.pack g (hv.integrable _) hg]
    change (∫ U, (g∘Q) U ∂_)=_
    rw [F.pack (g ∘ Q) (h.integrable _) (fun i hj U=> ?_)]
    · simp_rw [Function.comp_apply,displayed]
      have hp : MeasurePreserving (s*·) (F.order G) (F.order G) := measurePreserving_pi (fun _=> G.probHaar) (fun _=> G.probHaar) fun i=> measurePreserving_mul_left G.probHaar (s i) -- name adjust
      exact hp.integral_comp (Homeomorph.mulLeft s).measurableEmbedding (fun i=>g (F.drape i))
    change g (Q _)=g (Q U); rw [dodge F s _ _ hj,hg i hj]
lemma grove (v:σθ→ G.El)(B:N)(ht:∀ i,v (S.ratio.embed i)=1) : canoe (S:=S) F (gauge v B)=canoe (S:=S) F B:=by
    funext i; unfold canoe Forest.foldAt; dsimp only [Lattice.gauge]; rw [travel_gauge,travel_gauge,F.hike_root, F.hike_root,ht,ht]; group
include hd h
lemma tonic : S.Inner (boundPress S R V) := by
    intro k he U; unfold boundPress; rw [Push.SectorMeasure.Presented.lawful_gi h.lawful,← S.covary hd k R.beta U V]; rw [show Lattice.gauge (k ∘ S.ratio.embed) V=V from funext (fun i=>by simp [Lattice.gauge,he])]
lemma journey : Moving V R S (Sweet S) Set.univ Q (fun _=>1) := by
    refine ⟨MeasurableSet.univ,(pedaling F s).measurable,Envelope.const _,?_⟩
    intro A Y hA hY ht hy he hf; let g:=boundPress S R V; let w:= Y.indicator g; let f(i):= g (Q i)
    have hg := bound_ink h; have hw:Envelope w:= Envelope.piece hY hg (Envelope.const _)
    have hv := tribute F s w (fun t hv U=>by
           unfold w; by_cases hh:U∈Y; rw [Set.indicator_of_mem ((hy t hv U).1 hh),Set.indicator_of_mem hh]; exact tonic hd h t hv _
           rw [Set.indicator_of_notMem ((hy t hv U).not.mp hh),Set.indicator_of_notMem hh]) hw
    change _ ≤ (∫ U,w U∂prior G _); rw [← hv]
    simp_rw [one_mul]; obtain ⟨b,hb⟩:=hg.cost; obtain ⟨t,hc⟩:=hw.cost
    apply integral_mono ((show Envelope f from ⟨hg.meas.comp (pedaling F s).measurable,b,fun i=>hb _⟩).integrable (prior G _) |>.indicator hA) ((show Envelope (w∘Q) from ⟨hw.meas.comp (pedaling F s).measurable,t,fun i=>hc _⟩).integrable _)
    intro i; by_cases hw:i∈A
    · exact (Set.indicator_of_mem hw f |>.trans (Set.indicator_of_mem (hf hw) g).symm).le
    rw [Set.indicator_of_notMem hw]; exact Set.indicator_nonneg (fun i _=> bound_positive h _) _
end YM.MSbar.Heath
