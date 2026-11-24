import YM.SignedWilsonExpansion.ValueT
namespace YM.SignedWilsonExpansion.AxisChoice
/-! The projected spectral density, before and after reading. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Koszul MS.Plane MS.Plane.Flux MS.Landau MS.High MS.Landau.Detect MS.Landau.Detect.Mark
open FVA2 FVA2.Lambda Area Walk Bubble Heter TreeLine
open scoped Classical Topology ContDiff BigOperators RealInnerProductSpace
local notation "P" => FourP
local notation "T" => tangent
local notation "Z" => Momentum.sq
local notation "e" => AxisChoice.direction
variable {h:ℝ→ℝ} (he: ContDiff ℝ ∞ h) (k:P)(i j:Test)

local notation "Wk"=> fun i j p q=> TraceE.complete h 1 2 p q i j k
local notation "U" => fun i j p q => UX h i j p q k
local notation "Ta" => fun i j p q => TX h i j p q k
local notation "V" => fun i j p q => VX h i j p q k
local notation "R" => fun i j p q => RX h i j p q k
local notation "T₁" => fun i j p q => TX h j i q p k
local notation "R₁" => fun i j p q => RX h j i q p k
local notation "V₁" => fun i j p q => VX h j i q p k
lemma compose : Wk=Ta+T₁+V+V₁+U+R+R₁:= funext (fun i=>funext fun j=> funext fun _=>funext fun q=>assembly .. )
def salary (h:ℝ→ℝ) (L B:ℝ):ℝ:=
    128* L^2*h L-96*L * B*h L -96*(h L*L)^2*B*(L-B)
include he
lemma prof : Smooth Wk := by rw [ compose k ]; exact ((warmT k he).add (warmT k he).swaps |>.add (warmV k he) |>.add (warmV k he).swaps |>.add (warmU k he) |>.add (warmR k he) |>.add (warmR k he).swaps )
lemma done_price : bill Wk= salary h (Z k) (disk k):= by
    have heq{p q: Panel}(hp:Smooth p)(ht:Smooth q): bill (p+q)= bill p+bill q:= add_b hp ht
    have p:Smooth Ta:= warmT k he; have q:Smooth V:=warmV k he; have r:Smooth R:= warmR k he; have u:Smooth U:=warmU k he
    let A:=Ta+T₁+V+V₁+U; have hA:Smooth (Ta+T₁+V+V₁+U):= p.add p.swaps |>.add q |>.add q.swaps |>.add u
    rw [compose k, heq (show Smooth (Ta+T₁+V+V₁+U+R) from hA.add r) (show Smooth _ from r.swaps), heq hA r,
        heq (show Smooth (Ta+T₁+V+V₁) from p.add p.swaps |>.add q |>.add q.swaps) u,
        heq (show Smooth (Ta+T₁+V) from p.add p.swaps |>.add q) (show Smooth _ from q.swaps),
        heq (show Smooth (Ta+T₁) from p.add p.swaps) q,
        heq p (show Smooth _ from p.swaps)]
    rw [sym_b p,sym_b r,sym_b q,Tprice he k,Uprice he k,Rprice he k,Vprice he k ]; unfold salary weight; ring

omit he
variable {G:Gauge}(t:ℝ)
open TorchE MarkTop MS.Pearl MS.Emit MS.Plane.Domain MS.Land MS.Rake
local notation "Π₊" => MS.Landau.covMeasure Axis
local notation "Σx" => (ℝ×ℝ)
local notation "Tx" => MarkRows.packet

abbrev photoX (G:Gauge) (k:P) (t:ℝ)(i j:Test): Σx→ ℂ:= fun x=> rawE t k 1 2 G (AxisChoice.direction i) (AxisChoice.direction j) ( x.1 • T i ) ( x.2 • T j )
abbrev probeX (G:Gauge) (k:P) (t:ℝ)(x:P) (i j:Axis)(y:P):ℂ:= reading 2 (fun z:ℝ=> rawE t k 1 2 G i j (z • x) (z • y))

lemma true_price :
    (∑ i:Test,∑ j:Test,mixed ( photoX G k t i j ))= (↑( G.casimir * Shells.hot t (Z k) *2*salary (amp t) (Z k) (disk k) ):ℂ):= by
    let F(p:P)(i j:Axis)(x y:P):= TraceE.complete (amp t) 1 2 x y i j p
    let B(p:P):= F p
    have hp(p:P):Smooth (B p) := prof smooth_amp p -- check order
    let L:= Complex.ofRealCLM.comp ((G.casimir* Shells.hot t (Z k)) • ContinuousLinearMap.id ℝ ℝ)
    have he(i j:Test): photoX G k t i j = (fun x=> L (daily (B k) i j x + daily (B (-k)) i j x)) := rfl
    let c:= G.casimir* Shells.hot t (Z k)
    have hx(i j:Test): mixed (photoX G k t i j) = ((↑c:ℂ)* (↑(( tooth (daily (B k) i j)+ tooth (daily (B (-k)) i j):ℝ)):ℂ)):= by
       let f:= daily (B k) i j; let q:=daily ( B (-k) ) i j; have hm: ContDiff ℝ ∞ (fun x=> f x+q x):=( hp k i j ).add (hp (-k) i j)
       rw [ he ]; change mixed ( L ∘ (fun x=>f x+q x) )=_; rw [read_mixed (L.contDiff.comp hm),tooth_linear hm L,tooth_add (F:=f) (H:=q) (hp _ i j) (hp _ i j) ]; exact Complex.ofReal_mul ..
    simp_rw [ hx, ← Finset.mul_sum, ← Complex.ofReal_sum,Finset.sum_add_distrib ]; change _ * ((bill (B k)+ bill (B (-k)):ℝ):ℂ)=_
    unfold B F; rw [ done_price (TorchE.smooth_amp (t:=t)) k, done_price (TorchE.smooth_amp (t:=t)) (-k), dial_neg k, MS.Landau.sq_neg ]; unfold c; push_cast; ring
lemma packet_read (f:Σx→ℂ)(p:Σx): ray_read f p= reading 2 (fun x:ℝ=> f (x • p)) := by unfold ray_read reading; norm_num
def slopeQ (k:P)(G:Gauge)(t:ℝ):ℂ:= ∑ i:Test,∑ j:Test,mixed (photoX G k t i j)
lemma type_mix : mixed (photoX G k t i j)= ((1/2):ℝ) • ( probeX G k t (T i) (e i) (e j) (T j) - probeX G k t (T i) (e i) (e j) (- T j) ):= by
    unfold mixed probeX; simp_rw [ packet_read ]; unfold photoX; simp only [ofXY,Prod.smul_mk, Prod.mk_add_mk,Prod.mk_sub_mk,mul_zero,zero_sub, sub_zero,one_mul,mul_one,smul_eq_mul,smul_neg,add_zero,zero_add,mul_neg,neg_smul]

variable {B : MS.Land.Booked (Press.portDeck G)} (M:MS_Data G B)(simple:G.Simple) (A:G.ColorIndex)
local notation "Φ" => spaceD G
include simple M
include A
private lemma probe_paid (i j:Axis)(p q:P) : Integrable (fun k=> probeX G k t p i j q) Π₊:= by
    let w:=[ W i A p, W j A q ]; let z:MarkRows.I (Press.portDeck G)→ℝ:=Energy.called 1 2 G
    have H := TorchE.trc_integrable (a:=1) (b:=2) (n:=2) M (0,t) w
    unfold probeX; simp_rw [ ← show ∀ k, reading 2 _=reading 2 (fun u:ℝ=>rawE t k 1 2 G i j (u • p) (u • q)) from fun k=> (focus_mark (A:=A) (p:=p) (q:=q) (i:=i) (j:=j) (a:=1) (b:=2) (k:=k) M simple (0,t)) ]; exact H
lemma paid (i j:Test) : Integrable (fun k=> mixed (photoX G k t i j)) Π₊:= by
    simp_rw [type_mix]; exact ((probe_paid t M simple A (AxisChoice.direction i) (AxisChoice.direction j) _ _).sub ( probe_paid t M simple A _ _ _ _ )).smul (1/2:ℝ)
lemma paid_price : Integrable (fun k=>slopeQ k G t) Π₊:= by
    unfold slopeQ; exact integrable_finsetSum _ fun i _=> integrable_finsetSum _ fun j _=> paid t M simple A i j
def probeAct (A:G.ColorIndex)(F:Law G):ℂ:=
      ∑ i:Test, ∑ j:Test, ((1/2):ℝ) • (torch 2 F [W (e i) A (T i),W (e j) A (T j)]- torch 2 F [ W (e i) A ( T i ), W (e j) A ( -T j ) ])
lemma paceAct (S:Clock ℝ) :
      probeAct A ( MS.Plane.Domain.recu Φ 0 1 ( Outlook.Archive 4 M.bulk ) ( Tx M (Energy.called 1 2 G) ) 2 S )=
           ∫ k:P,slopeQ k G S.2∂Π₊:=by
    unfold slopeQ probeAct
    rw [integral_finsetSum]; swap; · exact fun i _=> integrable_finsetSum _ fun j _=> paid S.2 M simple A i j
    refine Finset.sum_congr rfl fun i hi=>?_ ; rw [ integral_finsetSum _ ( fun j _=> paid S.2 M simple A i j ) ]; refine Finset.sum_congr rfl fun j _=>?_; simp_rw [type_mix]; rw [ integral_smul, integral_sub ( probe_paid S.2 M simple A _ _ _ _ ) ( probe_paid S.2 M simple A _ _ _ _ ), TorchE.projector M simple S,TorchE.projector M simple S ]
-- actual mark scale derivative starts projector.

end
end YM.SignedWilsonExpansion.AxisChoice
