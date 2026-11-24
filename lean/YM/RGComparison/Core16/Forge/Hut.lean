import YM.RGComparison.Core16.Forge.Ring
import YM.Push.GRID_APPROXIMATION.Cone
import YM.Push.FREE_RESOLVENT.Midpoint
import YM.Further.ROOTED_INTERACTING_REMAINDER.Vault
import YM.Work.E01

/-!
# This SEAM specializes true tilted-gas criteria. Proto-MM. V global sup-link budget (unscaled).
Cost graph includes every physical predictor read, no average or coarsening assumption.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Forge.Hut
open Filter Function Finset Lattice RG Tree Wilson MeasureTheory Push.AbsoluteSums.Animals Pressure
open Precision Push.BetaTransport Push.GridApprox
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge} {c f: Side} (S:StepData c f) (T:Forest S.ratio) (V:Config G c)
abbrev Rooms (c f:Side):= (Face (Per f)) ⊕ Edge (Site c)

def pad {S:StepData c f} (T:Forest S.ratio)(i:T.Free):=i.val.1
def hold (x: Site c):= S.ratio.embed x
def root := Sum.elim (Prod.fst:Face (Per f) → Site f) (hold S ∘ (Prod.fst: Edge (Site c) → Site c))

def seam : Base G f T.Free (Rooms c f) S.Choices:= {
    loc:=pad T
    band:=root S
    choices s x:= S.likelihood (T.drape x) s
    cost s x:= Sum.elim (fun i=> G.price (faceValue (T.drape x) i)) (fun i=> linkEnergy S (V i*(S.prediction (T.drape x) s i)⁻¹)) }
local notation "B" => seam S T V
lemma action_eq t x: (B).action t x=energy (T.drape x)+ tagEnergy S t (T.drape x) V:= Fintype.sum_sum_type ..
lemma cooks (x:Sky G T.Free)(t:S.Choices)(j:Rooms c f):0≤(B).cost t x j:= Sum.rec (fun _=> (G.price_range _).1) (fun _=> (link_estimate S).nonneg _) j

def width (P:Patch):= P.L.val+ macroR P + reach P + 2
def quota:ℕ:= Fintype.card Axis + Fintype.card PlaqAxes
lemma floor_pos : 0<quota:= by let a:Fintype Axis:=inferInstance; unfold quota; have := Fintype.card_pos (α:=Axis); omega

private lemma limit {I k: Type}[Fintype I][Fintype k]{x:I→ Site f}{y:I→k}(h:Injective fun z=> (x z,y z)): Coverage (Fintype.card k) x:=by
   intro j
   let P:= univ.filter fun i : I=>x i=j
   refine (card_image_of_injOn (f:=y) (s:=P) (fun u hu v hv hh=> h (Prod.ext ((mem_filter.mp (mem_coe.mp hu)).2.trans (mem_filter.mp (mem_coe.mp hv)).2.symm) hh))).symm.le.trans (card_le_univ _)
lemma root_price : Coverage quota (root S):= by
    unfold quota; rw [Nat.add_comm,← Fintype.card_sum]
    apply limit (y:=Sum.elim (fun p : Face (Per f)=> Sum.inl p.2) (fun e:Edge (Site c)=> Sum.inr e.2)); rintro (⟨a,b⟩|⟨a,b⟩) (⟨d,e⟩|⟨d,e⟩) he
    all_goals simp [root,hold] at he
    · rw [he.1,he.2]
    rw [he.2, (show Function.Injective S.ratio.embed from fun i j h=> by simpa only [S.ratio.embed_parent] using congr_arg S.ratio.parent h) he.1]
lemma pad_price : Coverage quota (pad T):= fun i=>(limit (x:=pad T) (y:=fun j: T.Free=>j.val.2) (fun _ _ he=> Subtype.ext he) i).trans (Nat.le_add_right ..)

variable {S T} {x y:Sky G T.Free}

lemma box_sep {i j:Site f}{R:ℕ}(h:i∈window j R) : separation j i≤R:=by
    obtain ⟨a,ha,rfl⟩:=h
    rw [separation_comm]; change pdist (_-j)≤_; rw [add_sub_cancel_right]
    exact Work.E01.pdist_wrap_le ha
lemma neighbour (e:Edge (Site c)) : separation (hold S e.1) (hold S (e.1+step e.2))≤ S.patch.L.val:=by
    unfold hold; rw [FreeResolvent.Mid.upto]; have hz: separation e.1 (e.1+step e.2)≤1:=by rw [separation_comm,separation,add_comm,add_sub_cancel_right]; exact pdist_step _
    exact (Nat.mul_le_mul_left S.patch.L.val hz).trans (Nat.le_of_eq (mul_one _))

lemma wires {m:ℕ}{z:Site f}(h:∀ i∈neighborsOf (pad T) m z,x i=y i) {v: Site f}{r:ℕ}(hv:separation z v+r≤m):Agrees (window v r) (T.drape x) (T.drape y):=by
    intro i hi hi'; by_cases hk:i∈T.trunks
    · rw [T.on_tree x ⟨_,hk⟩,T.on_tree y ⟨_,hk⟩]
    let j:T.Free:= ⟨i,hk⟩; change T.drape x j.val=T.drape y j.val; rw [T.off_tree,T.off_tree]; apply h; exact (member ..).mpr ((separation_triangle z v i.1).trans ((Nat.add_le_add_left (box_sep hi) _).trans hv))
lemma stele {b:Face (Per f)}(h:∀ i∈neighborsOf (pad T) (width S.patch) b.1,x i=y i):
    faceValue (T.drape x) b=faceValue (T.drape y) b:= by
    apply travel_local
    intro i hi hi'; by_cases hk:i∈T.trunks
    · rw [T.on_tree x ⟨_,hk⟩, T.on_tree y ⟨_,hk⟩]
    let j:T.Free:= ⟨i,hk⟩; change T.drape x j.val=T.drape y j.val; rw [T.off_tree,T.off_tree]; apply h; exact (member ..).2 ((Work.E01.sep_touched b _ (List.mem_toFinset.mpr hi)).trans (Nat.le_add_left ..))
lemma stitch (hS:S.patch.Branches S.kernel G){b:Edge (Site c)} {t s:S.SitesChoice} (hp:t b.1=s b.1)(hq:t (b.1+step b.2)=s (b.1+step b.2)) (h:∀ i∈neighborsOf (pad T) (width S.patch) (hold S b.1), x i=y i): S.connector (T.drape x) t b= S.connector (T.drape y) s b:= by
    apply connector_dep S hS _ _ _ hp hq
    · apply wires h; unfold hold; rw [separation_self]; unfold width; omega
    · apply wires h; unfold width; have he:=neighbour (S:=S) b; unfold hold at *; omega
end YM.RGComparison.Core16.Forge.Hut
