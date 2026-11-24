import YM.RGComparison.Core16.Parcel.Pose
import YM.RGComparison.Core16.Silk.Parcel
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Usual
/-!
# Connect Θ grids throughout period estimates
Preserves Oversets using determinant-free algebra on real-sector pricing. Certified foreclosure
roles; real path and loop not projected through P.pad to pay at small period unless lemma.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Silk
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity
open Push.AbsoluteSums.Animals Precision Finset
open PhysicalNext.Repeat Further.PhysicalPeriodLimitF933 Macrame Parcel Parcel.Oven
open scoped Topology ContDiff PowerSeries Classical BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{A D I J T k:Type}[Fintype I][Fintype J]
   {C c F f: Side} {P:Patch} (K:KernelChoices) {W:Oven P} {X:W.Form G} {e : f.val=c.val*P.L.val} {E:F.val=C.val*P.L.val} {d : ℕ}
   (hC:C.val=c.val*d)(hc:2 ≤ c.val)
local notation "L0"=> Lace.project (h:=e) (H:=E) hC hc
local notation "S"=> StepData.mk P K E
local notation "S0"=> StepData.mk P K e

open Forge.Hut
-- Direction lift to larger period

def vectorCover {c C:Side}(h:c.val∣C.val)(u:Directions G c) : Directions G C:= u ∘ Prod.map (splitter h) id

def plough (hd:f.val∣ F.val) (he:c.val∣ C.val) : Rooms C F→ Rooms c f:= Sum.map (Prod.map (splitter hd) id) (Prod.map (splitter he) id)
lemma zoom (E:F.val=C.val*P.L.val)(e:f.val=c.val*P.L.val)(hC:C.val=c.val*d):f.val∣F.val:= ⟨d,Deck.fineP e E hC⟩
set_option quotPrecheck false
local notation "∂L"=> (zoom E e hC)
local notation "∂B"=> (show c.val∣ C.val from ⟨d,hC⟩)
local notation "U#"=> plough ∂L ∂B

def Pinnage {T:Ratio C F}{Y:Ratio c f}(h:f.val∣ F.val)(M:Forest T)(W:Forest Y):Prop:=∀ (i:Site F) (j:Axis),(i,j)∈M.trunks ↔ (splitter h i,j)∈W.trunks
def projectStem {T:Ratio C F}{Y:Ratio c f}(h:f.val∣ F.val){M:Forest T}{W:Forest Y}(U:Pinnage h M W)(i:M.Free): W.Free:= ⟨(splitter h i.val.1, i.val.2),fun he=>i.property ((U i.val.1 i.val.2).2 he)⟩

variable {B' : Forest (StepData.mk P K E).ratio} {B: Forest (StepData.mk P K e).ratio} (hF:Pinnage (zoom E e hC) B' B)
    {hd : f.val∣ F.val}

include hc hC
lemma anchor_nest : Deck.Nest (zoom E e hC) (U#) (Hut.root S) (Hut.root S0):=by
   have ha : Deck.Nest ∂L (splitter ∂L) id id:=⟨fun _=>rfl,fun x i h=>⟨_,h.symm,rfl⟩,fun _ _ _ h=>h⟩
   have hb: Deck.Nest ∂L (splitter ∂B) (hold S) (hold S0):=by
      let L:= L0; let P' :=L.R; let q:=L.r
      refine ⟨L.stake,fun x i h=>?_, fun x i h₁ h₂=>?_⟩
      · change q.embed i=L.high.cut x at h; let y:=P'.parent x; have hy:L.low.cut y=i := by rw [show L.low.cut y=q.parent _ from (L.position x).symm,← h,q.embed_parent i]
        have hV : ¬leaf P' x:= by intro he; apply (L.fork x).1 he; rw [← h]; rw [q.embed_parent] 
        exact ⟨y,hy,(Classical.not_not.mp hV|>.symm)⟩
      change P'.embed x=P'.embed i at h₂; exact (P'.embed_parent x).symm.trans ((congr_arg P'.parent h₂).trans (P'.embed_parent i))
   exact Deck.Nest.sum (ha.pr (E:=PlaqAxes)) (hb.pr (E:=Axis)) -- Π binder maybe
include hF
-- all sizes admitted by Lem t>L. here θ seam uses Steady. Z.u rates after cp5.
set_option maxHeartbeats 800000 in
omit hc in
lemma role_nest : Deck.Nest (zoom E e hC) (projectStem ∂L hF) (Hut.pad («S»:=S) B') (Hut.pad («S»:=S0) B):= by -- abbrev? replace
   refine @Deck.Nest.mk f F (zoom E e hC) B.Free B'.Free (projectStem ∂L hF) (Hut.pad («S»:= S) B') (Hut.pad («S»:=S0) B) ?_ ?_ ?_
   · exact fun _=>rfl
   swap; intro x i h he; exact Subtype.ext (Prod.ext (show x.val.1=i.val.1 from he) (show x.val.2=i.val.2 from congr_arg (fun r:B.Free=> r.val.2) h))
   intro x i h; have hx : (x,i.val.2)∉ B'.trunks:= by rw [hF x i.val.2]; rw [show splitter ∂L x=i.val.1 from h.symm]; exact i.property
   exact ⟨(⟨(x,i.val.2),hx⟩: B'.Free), Subtype.ext (Prod.ext h.symm rfl),rfl⟩

omit hc hC hF in
lemma NestFlow {I J : Type}[Fintype I][Fintype J] {s:J→ I}{x:J→ Site F}{y:I→Site f}(H:Deck.Nest hd s x y)(u:Site F)(v:Site f)(hu: v=splitter hd u){k}(hk:2*k < f.val): SliceMap (neighborsOf x k u) (neighborsOf y k v) s:= by
    subst v; refine ⟨fun i h=> ?_, fun i hi j hj he=> H.point hk u _ _ ((member ..).1 (mem_coe.mp hi)) ((member ..).1 (mem_coe.mp hj)) he, fun i hi=> ?_⟩
    · apply mem_coe.mpr ((member ..).2 ?_); rw [←H.footing]; exact (Deck.less hd ..).trans ((member ..).1 (mem_coe.mp h))
    obtain ⟨j,he,hk⟩:= H.esc u i; exact ⟨j,mem_coe.mpr ((member ..).2 (hk.trans_le ((member ..).1 (mem_coe.mp hi)))),he⟩
omit hF hc hC [Fintype I] [Fintype J] in
lemma within_one {hd : f.val∣ F.val}{s:J→ I}{x:J→ Site F}{y:I→Site f}(H: Deck.Nest hd s x y)(u:Site F) {k}(hk:2*k < f.val) : Set.InjOn s {i|separation u (x i)≤k} := fun i hi j hj he=> H.point hk u i j hi hj he
set_option maxHeartbeats 800000 in
lemma point_cover (z:Site F)(i:W.Xways) : Option.map (projectStem ∂L hF) (W.listPtr K (d:=E) B' z i)= W.listPtr K (d:=e) B (splitter ∂L z) i:=by
    let u:= lift (i.1-hold (W.stance K) 0); unfold listPtr; dsimp only; by_cases hw:u∈ Lattice.box (Hut.width P)
    swap; rw [if_neg hw, if_neg hw]; rfl
    rw [if_pos hw,if_pos hw]
    let j: Edge (Site F):=(wrap F u+z,i.2); let l:Edge (Site f):= (wrap f u+splitter ∂L z,i.2)
    have he:splitter ∂L j.1=l.1:= ((L0).high.rooted z u)
    have h : j∈B'.trunks↔l∈B.trunks:= by exact (he ▸ (hF j.1 i.2) : j∈B'.trunks ↔ (l.1,i.2)∈B.trunks)
    by_cases hz:j∈B'.trunks
    · rw [dif_pos hz,dif_pos (h.1 hz)]; rfl
    rw [dif_neg hz,dif_neg (mt h.2 hz),Option.map_some]; apply congr_arg Option.some; exact Subtype.ext (Prod.ext he rfl)

set_option maxHeartbeats 800000 in
lemma ministry {X:Shelf G (PlaqAxes⊕Axis) W.Xways}(hv:2*X.sector.b < f.val)(u:Directions G c) : Overset (P:=parcela K (d:=E) X B' (vectorCover ∂B u)) (Q:=parcela K (d:=e) X B u) (projectStem ∂L hF) (U#):= by
    let v:= vectorCover ∂B u; let L:= L0; let T:= parcela K (d:=E) X B' v; let W':=parcela K (d:=e) X B u; let s:= U#; change Overset T W' (projectStem ∂L hF) s; constructor 
    · intro a; cases a <;> rfl
    · intro a; cases a <;> rfl
    · intro a i; change Option.map _ (W.listPtr K (d:=E) B' (Hut.root S a) i)=W.listPtr K (d:=e) B (Hut.root S0 (s a)) i; rw [show Hut.root S0 (s a)= _ from (anchor_nest (E:=E) (e:=e) K hC hc |>.footing a).symm]; exact point_cover K hC hc hF ..
    · intro a; exact NestFlow (role_nest K hC hF) _ _ ((anchor_nest K hC hc (e:=e) (E:=E)).footing a).symm hv
    intro i; exact NestFlow (anchor_nest K hC hc (e:=e) (E:=E)) _ _ ((role_nest K hC hF).footing i).symm hv

end YM.RGComparison.Core16.Silk
