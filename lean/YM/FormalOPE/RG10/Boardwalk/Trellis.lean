import YM.FormalOPE.RG10.Boardwalk.Regatta
import YM.FormalOPE.RG10.Profile.Press
/-!
 # Frame orientation on finite **moving** positions at fixed arity
Home Plate in real profile basis. `Pose.Prior.Attentive`, compatibility *derived* from
K.fc test estimates even after diverging input.H.Frame. Need preserve Roll.H.* held.
Use all cutoffs along l, shapes here need supplied budgets from generators; without those
results only conditional. Do NOT infer anything for collisions. Can use e.g. in entire
program at far probes with exp(t) subpower; use enlarged Λ clock ensuring Z poly on all
slot costs via restatement. See Gliss. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Boardwalk.Trellis
open Filter Function Finset PowerSeries Clearing Ledger Rates InversionTop
open Carryon PertExtension Position Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric PertExtension.Position Triangle Lawn
open RG10.Profile Gliss Gazebo Matrix
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge}{F:Frames G}{I:Type*}{l:Filter I}{P:Path l}{r d n:ℕ}
variable (D:Stock F)
local notation "Ψ" d=>Mark (Deck F d) PertExtension.Physical.Profile.n
local notation "κ" d=>Deck F d
local notation "ins" d=> PertExtension.Position.insert (Deck F d) PertExtension.Physical.Profile.n
variable {x y v u:I→ Mark (Deck F d) PertExtension.Physical.Profile.n→fps}
variable {L M:I→ Matrix (Deck F d) (Deck F d) fps}
-- dynamic test-trace in chosen T with actual embeddings and derivative orders.
def Stage (P:Path l)(r:ℕ)(x y:I→Mark (Deck F d) PertExtension.Physical.Profile.n→fps)(s:I→Test n) := ∀ v:Fin n→Deck F d,Posi P r (fun i=> x i (task (s i) v)) (fun i=> y i (task (s i) v))
variable {s:I→ Test n}
namespace Stage
variable (h:Stage P r x y s)
include h
lemma seen (hz:∀ i j,Posi P r (fun v=>L v i j) (fun v=> M v i j)): Stage P r (fun k=>(ins d) (x k) (L k)) (fun k=> (ins d) (y k) (M k)) s:= by
 intro v
 change Posi P r (fun i=>∑ b:Fin n→Deck F d, x i (task (s i) b)*∏ k:Fin n,L i (v k) (b k)) (fun i=>∑ b:Fin n→Deck F d, y i (task (s i) b)*∏ k:Fin n,M i (v k) (b k))
 exact Posi.sum (univ:Finset (Fin n→ Deck F d)) (fun j _=> (h j).mul (Posi.product (univ:Finset (Fin n)) (fun i _=> hz (v i) (j i)))) -- duplicate binder
lemma fit (he:x=ᶠ[l] v)(ht:y=ᶠ[l] u):Stage P r v u s:= fun q=> (h q).fits (he.mono fun _ hi=> congr_fun hi _) (ht.mono fun _ hi=>congr_fun hi _) -- lint
lemma transit (he:Stage P r y v s): Stage P r x v s:= fun q=> (h q).transit (he q)
lemma calendar {p q:I→ Warp} (ht:Posi P r (fun i=>(p i).x) (fun i=>(q i).x)): Stage P r (fun i=> (p i).charge ∘ x i) (fun i=> (q i).charge ∘ y i) s:= fun z=> Posi.century (h z) ht
omit h
lemma settled (a:Test n) (he:Answers P r x y ⟨n,a⟩): Stage P r x y (fun _=>a):= he -- fix implicit
end Stage

-- first raw-array sibling test budget: `x` own procedure, `y` compare
-- after ANY admitted preprocessing. Here need valid orientation on all lengths and certificates.
variable {D}
def Alert (P:Path l)(D:Stock F)(r)(x y:I→ Mark (Deck F d) PertExtension.Physical.Profile.n→fps):= ∀ i∈(D d).tests, Gliss.Answers P r x y i
variable (hD : Official D)
namespace Alert
variable (hL:listens (l:=l) (D:=D) x)
include hL
-- for lane changes at x, then take if D.HVOSED
variable (hp:Alert P D r x y)
include hp hD
lemma repositioning (h:Stage P r x y s): Stage P r (fun i=> post D (x i)) (fun i=>post D (y i)) s:= h.seen (L:=fun i=> Carryon.posture D (x i)) (M:=fun i=> Carryon.posture D (y i)) (Gliss.posture (D:=D d) (hD.fresh d) hL hp)
omit hp hD
lemma uptake (hv : Tendsto (fun a=> Stg (L a) 0) l (𝓝 1)): listens (l:=l) (D:=D) (fun a=> (ins d) (x a) (L a)):= by
 let c:= PertExtension.Position.markIn (arity:= PertExtension.Physical.Profile.n) (J:=Deck F d) (D d).tests
 let a:= raw F d; let K := Carryon.Stg (1: Matrix (Deck F d) (Deck F d) fps) 0; have hK: K=1:= diag_at.trans diag_one.symm
 apply tendsto_pi_nhds.mpr; intro j; rcases j with ⟨j,u⟩; let b: Questionnaire (J:=Deck F d) (arity:=PertExtension.Physical.Profile.n) (D d).tests :=⟨j,u⟩
 let y(k) := (fun i=> constantCoeff (x k i)); have hx k : probe D ((ins d) (x k) (L k)) b= (ins d) (y k) (Stg (L k) 0) (c b):= by -- issue `ins` implicit fps? notation takes ℝ auto. Need `_root_.transpose`
      unfold Carryon.probe; simp only [Stg,coeff_zero_eq_constantCoeff_apply]; exact insert_constant ..
 have hu v:Tendsto (fun k=> y k (c ⟨j,v⟩)) l (𝓝 (a (c ⟨j,v⟩))) := tendsto_pi_nhds.mp hL ⟨j,v⟩
 have hw u v : Tendsto (fun k=> Stg (L k) 0 u v) l (𝓝 (K u v)):= by rw [hK]; exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hv u) v
 have ht : Tendsto (fun k=> probe D ((ins d) (x k) (L k)) b) l (𝓝 ((ins d) a K (c b))) := by
   simp_rw [hx]; exact tendsto_finsetSum _ (fun v _=> ((show Tendsto (fun k=> y k ⟨j.val,v⟩) l (𝓝 (a ⟨j.val,v⟩)) from hu _).mul (tendsto_finsetProd _ (fun t _=> hw (u t) (v t)))))
 apply ht.mono_right; apply le_of_eq; apply congr_arg; rw [hK]; convert! insert_one a (c b) using 4
 rename_i v w; by_cases he:v=w <;> simp [Matrix.one_apply,he]
omit hL
include hp in
lemma heard_fit (h : listens (l:=l) (D:=D) y) : listens (l:=l) (D:=D) x:= (testVector hp).flip.both _ h

-- Main use: precondition BAREs before canonical pose. Column bootstrap may
-- cost even spacing powers; no multiplier continuity required.
include hD hL
theorem credited (hx:∀ i,Upright (L i))(hv:Tendsto (fun i=>Stg (L i) 0) l (𝓝 1))
   (hu:Alert P D r (fun i=>(ins d) (x i) (L i)) y)(hw:Stage P r (fun i=>(ins d) (x i) (L i)) y s): Stage P r (fun i=>post D (x i)) (fun i=>post D (y i)) s:= by
 have he := uptake hL hv
 have hm := repositioning hD he hu hw -- order of args inspect
 apply hm.fit (loading hD L hL hx hv he) Filter.EventuallyEq.rfl
end Alert
end YM.FormalOPE.RG10.Boardwalk.Trellis
