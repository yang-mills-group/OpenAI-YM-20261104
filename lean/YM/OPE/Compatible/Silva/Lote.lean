import YM.OPE.Compatible.Silva.Dessert
/-!
# Scout links, rides and drape horizontality.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)(H:Even c.val)
local notation "μ"=> even_both S.ratio H
local notation "X!"=> forest S.ratio he
abbrev tripS := vforest S.ratio H he
abbrev Blocx:= (tripS S he H).Free
def innerB (i: Blocx S he H):(forest S.ratio he).Free:= ⟨i.val.val,mt (branch_rep S.ratio H he).mpr i.property⟩
lemma stationXY (i:Limb μ): (tripS S he H).Branch i↔ i.val∈ (forest S.ratio he).trunks:= branch_rep ..
def home (i:(forest S.ratio he).Free): Blocx S he H:=⟨pathX μ i.val,fun h=>i.property (resettle μ i.val ▸ staff_at S.ratio H he _ _ (branch_rep S.ratio H he |>.mp h))⟩ -- eq dir
@[simp] lemma home_inner (p:Blocx S he H):home S he H (innerB S he H p)=p:=Subtype.ext (path_id ..)
@[simp] lemma home_rot (p:(forest S.ratio he).Free)(k:Kv):home S he H (trainV S he H k p)=home S he H p:=Subtype.ext (path_ferry μ k p.val)
lemma StoH (p:edgeV f): (tripS S he H).Branch (pathX μ p)↔ p ∈ (forest S.ratio he).trunks:=by
    constructor
    · intro h; nth_rw 1 [resettle μ p]; exact staff_at S.ratio H he _ _ ((branch_rep ..).mp h)
    intro h; rw [stationXY]; obtain ⟨k,hk⟩:= (edgesK μ).who.mp ((edgesK μ).chosen p); change ferry k p=(pathX μ p).val at hk; rw [← hk]; exact staff_at S.ratio H he _ _ h
lemma padV (p:(forest S.ratio he).Free):trainV S he H ((edgesK μ).tick p.val) (innerB S he H (home S he H p))=p:=Subtype.ext (resettle μ p.val).symm
def EchoV (G: Gauge):Keys G (Blocx S he H)→L[ℝ] AxisChart G X!:= ContinuousLinearMap.pi fun i=> if dir μ i.val then -(ContinuousLinearMap.proj (home S he H i)) else ContinuousLinearMap.proj (home S he H i)
lemma echoVi (x: Keys G (Blocx S he H))(i:(forest S.ratio he).Free): EchoV S he H G x i= if dir μ i.val then -x (home S he H i) else x (home S he H i):=by rw [EchoV,ContinuousLinearMap.pi_apply];split<;>rfl
@[simp] lemma echoIn (x:Keys G (Blocx S he H))(p: Blocx S he H): EchoV S he H G x (innerB S he H p)=x p:=by rw [echoVi,home_inner,show dir μ (innerB S he H p).val=false from dir_here ..]; rfl
lemma echoRot (x:Keys G (Blocx S he H))(k:Kv): twirlF S he H k (EchoV S he H G x)=EchoV S he H G x:=by
    ext1 i; simp_rw [spinF0,echoVi, home_rot, show dir μ (trainV S he H k i).val= ((axisK k).flip i.val.2).xor (dir μ i.val) from stood ..]; cases h:dir μ i.val <;> cases hp:(axisK k).flip i.val.2 <;>simp
abbrev FetchS (G:Gauge): AxisChart G X!→L[ℝ] Keys G (Blocx S he H):= ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (innerB S he H i)
lemma echoFetch (u: AxisChart G X!)(h:∀ k,twirlF S he H k u=u): EchoV S he H G (FetchS S he H G u) = u:=by
    ext1 p; let k:= (edgesK μ).tick p.val; let i:=home S he H p; let q:=innerB S he H i; rw [← h k] -- accidentally recursive inner expression, undo
    rw [h]; have hh : u p= twirlF S he H k u p:=congr_fun (h k).symm p; rw [spinF0,show trainV S he H k p=q from ?_] at hh; swap; · rw [show p=trainV S he H k q from (padV S he H p).symm,train2]
    change EchoV S he H G _ p=u p; rw [echoVi]; exact hh.symm
lemma echoRoll (x:Keys G (Blocx S he H)): represent (cloak μ ((tripS S he H).rollX x))= fieldF X! (EchoV S he H G x):=by
    rw [cloak_e]; let P:= tripS S he H; let U:= EchoV S he H G x; let u:= P.rollX x; ext1 i; change Weir.coat μ (put u) i= _
    by_cases h:i∈ (forest S.ratio he).trunks
    · rw [show fieldF X! U i=1 from (forest S.ratio he).on_tree _ ⟨i,h⟩]; have hp:u (pathX μ i)=0:= P.keptZ _ x (⟨_,(StoH S he H _).mpr h⟩:P.Stable); unfold put Weir.coat; simp [*,PertExtension.Chart.expLinks]
    let p:(forest S.ratio he).Free:=⟨i,h⟩; let v:=home S he H p; rw [show fieldF X! U i= put U p from (forest S.ratio he).off_tree _ p]; unfold Weir.coat; rw [show put u (pathX μ i)=G.lieExp (x v) from congr_arg (G.lieExp) (P.kept 0 x v)]; change _= G.lieExp (U p); rw [show U p=_ from echoVi S he H x p]; change (if _ then _ else _)=G.lieExp (if dir μ i then -x v else x v); cases hk:dir μ i <;> simp [Work.F03.exp_neg_color]
end YM.OPE.Cascade.Rill
