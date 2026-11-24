import YM.XSpace.Fore
import YM.XSpace.Stairs
/-!
# Maximal X-space filter lump with profiles & center costs

Use `comap raw Box` not an origin. Power of all stretches, even owns arbitrary
arith sequences satisfying stretching.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Cirrus
open Filter Set Function Lattice Expense Further.FreeCovariance.KP Playpen
open scoped Topology BigOperators Classical
variable {n:ℕ} {ι: Type*} {L:Filter ι}

def Front := comap (a (id:Mesh→Mesh)) (𝓝 0) ⊓ ⨅ k:ℕ,comap (fun i:Mesh=> a id i^k*sides id i) atTop
instance : Front.IsCountablyGenerated := by unfold Front; infer_instance
lemma frontier : Expense.Stretched Front id:= ⟨tendsto_iff_comap.mpr inf_le_left,fun _=> tendsto_iff_comap.mpr (inf_le_right.trans (iInf_le _ _))⟩
lemma goesFront {p:ι→Mesh}(S:Stretched L p):Tendsto p L Front:=by unfold Front; rw [tendsto_inf,tendsto_iInf]; exact ⟨tendsto_comap_iff.mpr S.endpt,fun k=>tendsto_comap_iff.mpr (S.pay k)⟩
instance good_front : Front.NeBot := goesFront (Stretched.runs (⟨3,by decide,1,⟨4,by decide,by decide⟩,by decide,by decide⟩:Run))|>.neBot

abbrev pack (n:ℕ):= Fin n→ Cover
structure Sample (n:ℕ) where
  F:Mesh
  layout: pack n
  center: Four ℝ
abbrev grab (q:Sample n) := q.F
abbrev unit (q:Sample n) := q.F.spacing
def welcome (q:Sample n) := q.center∈ q.F.Box
def familiar (q:Sample n) := q.F.rel q.layout q.center
variable (z : Points n)
abbrev Mask (n:ℕ):= principal {q:Sample n| welcome q}
def Gate := (comap grab Front ⊓ comap familiar (𝓝 z)) ⊓ Mask n
instance : (Gate z).IsCountablyGenerated:=by unfold Gate Mask; infer_instance
lemma liftG : Tendsto grab (Gate z) Front:= tendsto_iff_comap.mpr (le_trans inf_le_left inf_le_left)
lemma senseG : Tendsto familiar (Gate z) (𝓝 z):= tendsto_iff_comap.mpr (le_trans inf_le_left inf_le_right)
lemma welcomeG : ∀ᶠ i in Gate z,welcome i:= Eventually.filter_mono (show Gate z≤Mask n from inf_le_right) (eventually_principal.mpr fun _ h=> h)

lemma stepG : Tendsto unit (Gate z) (𝓝 0):= frontier.endpt.comp (liftG z)
-- dense matching table, no need diagonal families of resolutions, uncountable layouts

def river (p:Mesh): Four ℝ:=fun _=>p.size/8
lemma sits (p:Mesh): river p∈p.Box:=⟨le_refl _,fun j=>by change p.size /8≤p.size/4; linarith [p.size_pos]⟩
def draw (p:Mesh)(c:Four ℝ) : pack n:= Extraction.address p.spacing (z+Mesh.room c)
def ascend (p:Mesh):Sample n:=⟨p,draw z p (river p),river p⟩
lemma points_at : Tendsto (ascend z) Front (Gate z):=by
  rw [Gate,tendsto_inf,tendsto_inf]; refine ⟨⟨(tendsto_comap_iff.mpr (show Tendsto (grab ∘ ascend z) Front Front from tendsto_id)), (tendsto_comap_iff.mpr ?_)⟩, (tendsto_principal.mpr (Eventually.of_forall (fun i=> show ascend z i∈{q|welcome q} from sits i)))⟩; rw [tendsto_iff_dist_tendsto_zero]; apply squeeze_zero (fun i=>dist_nonneg) (fun i=> Mesh.upper_corner (x:=draw z i (river i)) i (river i) rfl)
  have hp:= frontier.endpt.const_mul ((4*n:ℝ)); rw [mul_zero] at hp; exact hp
instance : (Gate z).NeBot:= (points_at z).neBot

lemma gate_senses {F:Sample n→Prop}(h:∀ᶠ i in Gate z,F i): ∃ r:ℝ,0<r∧∀ᶠ p in Front,∀ (x:pack n)(c:Four ℝ), c∈p.Box→dist (p.rel x c) z<r→ F ⟨p,x,c⟩:=by
  unfold Gate at h; rw [eventually_inf_principal] at h; obtain ⟨s,h₁,t,h₂,H⟩:= mem_inf_iff.mp h; obtain ⟨k,hk,hK⟩:= mem_comap.mp h₁; obtain ⟨r,hr,hR⟩:=mem_comap.mp h₂; obtain ⟨a,ha,hh⟩:= Metric.mem_nhds_iff.mp hr
  refine ⟨a,ha,(show ∀ᶠ i in Front,i∈k from hk).mono fun p hp x c hc h=>?_⟩; apply (mem_setOf.mp (H.symm ▸ (show (⟨p,x,c⟩ : Sample n)∈s ∩ t from ⟨hK hp,hR (hh h)⟩))) hc
end YM.XSpace.Cirrus
