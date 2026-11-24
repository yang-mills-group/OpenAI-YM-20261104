import YM.SignedWilsonExpansion.Grid.Bread
namespace YM.SignedWilsonExpansion.Overlap
/-! The projected spectral density at mixed planes, before and after reading. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Koszul MS.Plane MS.Plane.Flux MS.Landau MS.High MS.Landau.Detect MS.Landau.Detect.Mark
open FVA2 FVA2.Lambda Area Walk Bubble Heter TreeLine AxisChoice
open scoped Classical Topology ContDiff BigOperators RealInnerProductSpace
local notation "P" => FourP
local notation "T" => side
local notation "Z" => Momentum.sq
local notation "e" => port
variable {h:ℝ→ℝ} (he: ContDiff ℝ ∞ h) (k:P)(i j:AxisChoice.Test)

local notation "Wk"=> fun i j p q=> TraceE.complete h 1 2 p q i j k
local notation "U" => fun i j p q => UX h i j p q k
local notation "Ta" => fun i j p q => TX h i j p q k
local notation "V" => fun i j p q => VX h i j p q k
local notation "R" => fun i j p q => RX h i j p q k
local notation "T₁" => fun i j p q => TX h j i q p k
local notation "R₁" => fun i j p q => RX h j i q p k
local notation "V₁" => fun i j p q => VX h j i q p k

-- before any angular average all at most quadratics in the three axis squares.
def salaryCross (h:ℝ→ℝ) (k:P):ℝ:=
   let X:=Z k; let A:=(k 0)^2; let B:=(k 1)^2; let C:=(k 2)^2; let f:=h X; let g:= deriv h X; let j:= deriv (deriv h) X
   f^2*(-32*X^3*A -384*X^3*B-64*X^3*C +96*X^2*A*B)+ f* (-16*X*B-64*X*C)+ g*(-16*X^2*B -64*X^2*C -64*X*(A+B+C)*C)+ j*(-32*X^2*(A+B+C)*C)
lemma silent (k:P): salaryCross h (-k)=salaryCross h k:= by simp [salaryCross, MS.Landau.sq_neg]
include he
lemma healthy : Ready Wk := by rw [ compose k ]; exact ((tReady he k).add (tReady he k).switch |>.add (vReady he k) |>.add (vReady he k).switch |>.add (uReady he k) |>.add (rReady he k) |>.add (rReady he k).switch )
lemma costPrice : survey Wk= salaryCross h k:= by
    have heq{p q: Panel}(hp:Ready p)(ht:Ready q): survey (p+q)= survey p+survey q:= aug  hp ht
    have p:Ready Ta:= tReady he k; have q:Ready V:=vReady he k; have r:Ready R:= rReady he k; have u:Ready U:=uReady he k
    let A:=Ta+T₁+V+V₁+U; have hA:Ready (Ta+T₁+V+V₁+U):= p.add p.switch |>.add q |>.add q.switch |>.add u
    rw [compose k, heq (show Ready (Ta+T₁+V+V₁+U+R) from hA.add r) (show Ready _ from r.switch), heq hA r,
        heq (show Ready (Ta+T₁+V+V₁) from p.add p.switch |>.add q |>.add q.switch) u,
        heq (show Ready (Ta+T₁+V) from p.add p.switch |>.add q) (show Ready _ from q.switch),
        heq (show Ready (Ta+T₁) from p.add p.switch) q,
        heq p (show Ready _ from p.switch)]
    rw [sw_f p,sw_f r,sw_f q,tS (h:=h) k,uS he k,rS he k,vS he k ]; simp only [salaryCross]; ring

omit he
variable {G:Gauge}(t:ℝ)
open TorchE MarkTop MS.Pearl MS.Emit MS.Plane.Domain MS.Land MS.Rake
local notation "Π₊" => MS.Landau.covMeasure Axis
local notation "Σx" => (ℝ×ℝ)
local notation "Tx" => MarkRows.packet

abbrev photoCross (G:Gauge) (k:P) (t:ℝ)(i j:AxisChoice.Test): Σx→ ℂ:= fun x=> rawE t k 1 2 G (port i) (port j) ( x.1 • T i ) ( x.2 • T j )

lemma photo_cost :
    (∑ i:AxisChoice.Test,∑ j:AxisChoice.Test,mixed ( photoCross G k t i j ))= (↑( G.casimir * Shells.hot t (Z k) *2*salaryCross (amp t) k ):ℂ):= by
    let F(p:P)(i j:Axis)(x y:P):= TraceE.complete (amp t) 1 2 x y i j p
    let B(p:P):= F p
    have hp(p:P):Ready (B p) := healthy smooth_amp p -- check order
    let L:= Complex.ofRealCLM.comp ((G.casimir* Shells.hot t (Z k)) • ContinuousLinearMap.id ℝ ℝ)
    have he(i j:AxisChoice.Test): photoCross G k t i j = (fun x=> L (assay (B k) i j x + assay (B (-k)) i j x)) := rfl
    let c:= G.casimir* Shells.hot t (Z k)
    have hx(i j:AxisChoice.Test): mixed (photoCross G k t i j) = ((↑c:ℂ)* (↑(( tooth (assay (B k) i j)+ tooth (assay (B (-k)) i j):ℝ)):ℂ)):= by
       let f:= assay (B k) i j; let q:=assay ( B (-k) ) i j; have hm: ContDiff ℝ ∞ (fun x=> f x+q x):=( hp k i j ).add (hp (-k) i j)
       rw [ he ]; change mixed ( L ∘ (fun x=>f x+q x) )=_; rw [read_mixed (L.contDiff.comp hm),tooth_linear hm L,tooth_add (F:=f) (H:=q) (hp _ i j) (hp _ i j) ]; exact Complex.ofReal_mul ..
    simp_rw [ hx, ← Finset.mul_sum, ← Complex.ofReal_sum,Finset.sum_add_distrib ]; change _ * ((survey (B k)+ survey (B (-k)):ℝ):ℂ)=_
    unfold B F; rw [ costPrice (TorchE.smooth_amp (t:=t)) k, costPrice (TorchE.smooth_amp (t:=t)) (-k), silent (h:=amp t) k ]; unfold c; push_cast; ring
def atBoth (k:P)(G:Gauge)(t:ℝ):ℂ:= ∑ i:AxisChoice.Test,∑ j:AxisChoice.Test,mixed (photoCross G k t i j)
lemma mixTwo : mixed (photoCross G k t i j)= ((1/2):ℝ) • ( probeX G k t (T i) (e i) (e j) (T j) - probeX G k t (T i) (e i) (e j) (- T j) ):= by
    unfold mixed probeX; simp_rw [ packet_read ]; unfold photoCross; simp only [ofXY,Prod.smul_mk, Prod.mk_add_mk,Prod.mk_sub_mk,zero_sub, sub_zero,mul_one,smul_eq_mul,smul_neg,add_zero,zero_add,mul_neg,neg_smul]

variable {B : MS.Land.Booked (Press.portDeck G)} (M:MS_Data G B)(simple:G.Simple) (A:G.ColorIndex)
local notation "Φ" => spaceD G
include simple M
include A
private lemma both_paid (i j:Axis)(p q:P) : Integrable (fun k=> probeX G k t p i j q) Π₊:= by
    let w:=[ W i A p, W j A q ]; let z:MarkRows.I (Press.portDeck G)→ℝ:=Energy.called 1 2 G
    have H := TorchE.trc_integrable (a:=1) (b:=2) (n:=2) M (0,t) w
    unfold probeX; simp_rw [ ← show ∀ k, reading 2 _=reading 2 (fun u:ℝ=>rawE t k 1 2 G i j (u • p) (u • q)) from fun k=> (focus_mark (A:=A) (p:=p) (q:=q) (i:=i) (j:=j) (a:=1) (b:=2) (k:=k) M simple (0,t)) ]; exact H
lemma budget_two (i j:AxisChoice.Test) : Integrable (fun k=> mixed (photoCross G k t i j)) Π₊:= by
    simp_rw [mixTwo]; exact ((both_paid t M simple A (port i) (port j) _ _).sub ( both_paid t M simple A _ _ _ _ )).smul (1/2:ℝ)
lemma budget_at : Integrable (fun k=>atBoth k G t) Π₊:= by
    unfold atBoth; exact integrable_finsetSum _ fun i _=> integrable_finsetSum _ fun j _=> budget_two t M simple A i j
def assayAct (A:G.ColorIndex)(F:Law G):ℂ:=
      ∑ i:AxisChoice.Test, ∑ j:AxisChoice.Test, ((1/2):ℝ) • (torch 2 F [W (e i) A (T i),W (e j) A (T j)]- torch 2 F [ W (e i) A ( T i ), W (e j) A ( -T j ) ])
lemma crossAct (S:Clock ℝ) :
      assayAct A ( MS.Plane.Domain.recu Φ 0 1 ( Outlook.Archive 4 M.bulk ) ( Tx M (Energy.called 1 2 G) ) 2 S )=
           ∫ k:P,atBoth k G S.2∂Π₊:=by
    unfold atBoth assayAct
    rw [integral_finsetSum]; swap; · exact fun i _=> integrable_finsetSum _ fun j _=> budget_two S.2 M simple A i j
    refine Finset.sum_congr rfl fun i hi=>?_ ; rw [ integral_finsetSum _ ( fun j _=> budget_two S.2 M simple A i j ) ]; refine Finset.sum_congr rfl fun j _=>?_; simp_rw [mixTwo]; rw [ integral_smul, integral_sub ( both_paid S.2 M simple A _ _ _ _ ) ( both_paid S.2 M simple A _ _ _ _ ), TorchE.projector M simple S,TorchE.projector M simple S ]


end
end YM.SignedWilsonExpansion.Overlap

