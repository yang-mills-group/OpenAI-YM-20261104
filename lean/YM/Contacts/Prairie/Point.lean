import YM.Contacts.Barrage.Horde
import YM.Contacts.Barrage.Flight
import YM.Branch.Pick
import YM.Next.FREE_KERNELS.Rack
import YM.LocalH.Haar
/-!
  # Formal lattice spacing progression

  For the spacing lattice minimal-log and LPT work. Names specify chronological
  words, with **last** step at the head (for Mark usage in the proofs). Function
  `column` supplies a true flat horizon at any of these stages. Not theorems
  about real levels or changing their clock; this is for independent LPT
  estimates. Keep smoothing J≥5 fixed per word/tree.
-/
namespace YM.Contacts.Prairie
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open Next.Free Milling.Lumen Barrage.Reserve
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G: Gauge}
structure Parcel (G:Gauge) where
   K:KernelChoices
   eligible (P:Patch): P.Branches K G
   Q: ChartRatio G
   valid: LocalRatio Q
   J: ℕ
   high: 5≤J
   T: MapPrices
   l: ℕ→ℝ
   γ: ℕ→ℝ
   b: ℕ→ℕ
   allowance: Catalog K T l γ b
   x: G.ColorIndex
   simple: G.Simple
namespace Parcel
structure Step where
  L: Side
  odd: Odd L.val
  prod: 3≤L.val
-- interpret words
abbrev Word:= List Step
variable (e:Parcel G) (p q:Word) (s:Step) (n:Side)
lemma feasible (h:G.Simple) (j:ℕ)(hj:5≤j){β:ℝ}(hβ:0<β):∃ e:Parcel G,e.J=j∧e.K.penalty=β:= by
   obtain ⟨K,hp,hq⟩:= Axial.viable G _ hβ; obtain ⟨T,l,v,b,hU⟩:= pledges K
   obtain ⟨Q,hQ⟩:= LocalH.actual G; obtain ⟨x⟩:= colorAvail G h; exact ⟨⟨K,hq,Q,hQ,j,hj,T,l,v,b,hU,x,h⟩,rfl,hp⟩
lemma ready : 4≤e.J:=le_trans (by decide : 4≤5) e.high
abbrev spit (R:Train e.J) : Flight e.J e.J:= ⟨s.L,s.odd,s.prod,e.ready,le_rfl,Nat.le_succ _,R⟩
def train : Word → Train e.J
   | [] => Train.top _
   | s::l => (e.spit s (train l)).land
abbrev path : Flight e.J e.J:= e.spit s (e.train p)
abbrev flag : Patch := ⟨s.L,e.J,e.ready,s.prod,s.odd⟩
def clip : Clip:= let v:=e.γ e.J; ⟨v,v/32,1,e.allowance.fit e.J, div_pos (e.allowance.fit _) (by positivity), by have ht:0<v:=e.allowance.fit _; linarith,zero_lt_one⟩
def column : Bed:= (e.allowance.bottom e.J e.ready e.clip le_rfl (e.train p)).choose
abbrev reach (e: Parcel G):ℝ≥0:= rentCheque e.T e.J
abbrev tax := purse e.T e.J
abbrev edge := e.T.η e.J
lemma coverage : (e.column p).covered e.reach (e.T.Ω e.J):= (e.allowance.bottom e.J e.ready e.clip le_rfl (e.train p)).choose_spec.2.1
lemma defined : Defined e.K.penalty (e.l e.J) (e.train p) (e.column p):= (e.allowance.bottom e.J e.ready e.clip le_rfl (e.train p)).choose_spec.1
lemma floor : Floor (e.column p) e.clip n e.edge (e.T.Ω e.J):= (e.allowance.bottom e.J e.ready e.clip le_rfl (e.train p)).choose_spec.2.2.1 n
lemma symmetry : ((e.column p).metric.acts n)ᵀ = (e.column p).metric.acts n := (e.floor _ _).symmetric.1
lemma top : (e.column []).diagonal.acts n=1:= (e.allowance.bottom e.J e.ready e.clip le_rfl (e.train [])).choose_spec.2.2.2.2 rfl n
lemma positive : 0<e.edge:= e.T.eta_pos _
lemma reach_pos : 0<e.reach:= rent_pos ..
lemma tax_pos : 0<e.tax:= purse_pos ..
lemma toll : (e.column p).metric.strip e.reach e.tax:= strip_mono (e.coverage p).2.1 le_rfl (le_max_right ..)
lemma whole : Whole (e.column p).metric:= ⟨e.reach,_,NNReal.coe_pos.mpr e.reach_pos,e.toll p⟩
abbrev traveler : StepData n (n*s.L):= Origin.sprig (e.flag s) e.K n
abbrev gas := ((e.path p s).duo e.K.penalty).A0
lemma rod (l:List Axis)(he:l.length≤e.J-2) : let L:=s.L; Row.strip (advanceC L (e.gas p s) l) e.reach (e.tax/(L.val:ℝ)^(1+l.length)):= strip_mono (((e.allowance.hop e.J e.J ⟨e.ready,e.ready,Or.inl rfl⟩ (e.path p s)).1 l he).1) le_rfl (by gcongr; exact le_max_right ..)
lemma awake: Awake G (e.flag s) e.K (e.column p) (e.column (s::p)) (e.gas p s) e.edge:= by
   refine ⟨e.eligible _,e.whole _,e.whole _,fun n=> ⟨fun x=> ((e.floor p n).uniform.1 _).1⟩,e.positive,e.symmetry _,fun n=>?_⟩
   exact (Next.Free.diagonal e.K (e.l e.J) (e.l e.J) (e.allowance.net _) (e.allowance.net _) (e.path p s) e.ready (e.column p) (e.column _) (e.defined _) (e.defined (s::p)) (c:=n) (f:=n*s.L) rfl).trial
lemma wheel_found : Nonempty (Wheel G (e.flag s) e.K (e.column p)):= by
   have he:=e.awake p s; obtain ⟨v,b,hv,hb,H⟩:= Origin.ceilCapacity _ _ _ he.alive e.reach_pos e.tax_pos.le e.positive
   obtain ⟨T,hU,hT⟩:= H (e.column p) (e.toll p) (fun n=>⟨he.handy n,he.gap n⟩); exact ⟨⟨T,hT,_,_, NNReal.coe_pos.mpr hv,hU⟩⟩
def wheel : Wheel G (e.flag s) e.K (e.column p):= Classical.choice (e.wheel_found p s)
end Parcel
end
end YM.Contacts.Prairie
