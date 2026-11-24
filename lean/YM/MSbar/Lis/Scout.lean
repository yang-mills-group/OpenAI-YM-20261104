import YM.MSbar.Lis.Province
import YM.MSbar.Chord.Intact
import YM.MSbar.MeasureP.Jams
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lis
open Function Filter Whisk Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Measuring Wave
open AnalyticBridge.VerifiedReset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n: Side}
variable (F : Positions (Primary n G)→ℝ)
local notation "X"=>Positions (Primary n G)
local notation "K"=>Primary n G
local notation "R"=>rim F
local notation "M"=>cell R
local notation "Y"=>buoy F 0
local notation "ℓ"=> Measuring.chart n G
variable (i j:Primary n G)
noncomputable def rope (i: Primary n G): Edge (Site n):=(i.1.1, Exterior.axisEquiv.symm i.1.2)
lemma curr (i:Primary n G): primary (rope i) i.2=i:=by rcases i with ⟨⟨x,i⟩,s⟩; obtain ⟨y,rfl⟩:= Exterior.axisEquiv.surjective i; simp [rope,primary]; rw [show Exterior.axisEquiv.symm (Exterior.coord y)=y from Exterior.axisEquiv.symm_apply_apply y]
lemma curb (a:Edge (Site n))(b : G.ColorIndex): rope (primary a b)=a:=by obtain ⟨x,i⟩:=a; unfold rope; change (x,Exterior.axisEquiv.symm (Exterior.axisEquiv i))=_; rw [Equiv.symm_apply_apply]
variable (u v:G.ColorIndex)
noncomputable def sun (G:Gauge)(i:G.ColorIndex) : G.Color:= EuclideanSpace.basisFun G.ColorIndex ℝ i
lemma sunny(u:G.ColorIndex): ‖sun G u‖=1:= (EuclideanSpace.basisFun G.ColorIndex ℝ).norm_eq_one _
lemma fair(A:Edge (Site n))(p:Axis)(f:Edge (Site n)→ℝ) : ((∑ i:Site n, f (i,p)):ℝ)= ∑ i:Primary n G, (if (i.1.2,i.2)=(Exterior.coord p,u) then f (rope i) else 0):=by
    unfold Primary Exterior.Body; rw [Fintype.sum_prod_type, Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_eq_single (Exterior.coord p)]; simp [rope,show Exterior.axisEquiv.symm (Exterior.coord p)=p from Exterior.axisEquiv.symm_apply_apply p]; exact fun x _ h=> by simp [h]
    simp
variable (h:ContDiffAt ℝ 2 F 0) (hG:G.Simple)
include h
lemma stream: buoy F 0 [i,j]= cell R (rope i) (rope j) (sun G i.2) (sun G j.2):=by
    let Z:=fderiv ℝ F; have he:DifferentiableAt ℝ Z 0:=(h.fderiv_right (show (1:WithTop ℕ∞)+1≤ 2 by norm_num)).differentiableAt (by norm_num)
    have h(i :Primary n G): bolt i=bead G (rope i) (sun G i.2):= (show bolt i= _ from congrArg _ (curr i).symm).trans (brand ..).symm
    unfold cell; rw [← h,← h]
    let A:=ContinuousLinearMap.apply ℝ ℝ (bolt j); change fderiv ℝ (A ∘ Z) 0 (bolt i) = _; rw [fderiv_comp _ A.differentiableAt he,A.fderiv];rfl
variable {a X':ℝ}{p:ℕ}
variable (e:G.ColorIndex)(hp:Ribbon (rim F))(ha:0 ≤ a)(hq:6≤p)(hx:∀ i: Primary n G,Yarn 1 (fun l:List (Primary n G)=> |buoy F 0 (i::l)| *swipe (Measuring.chart n G) a p (i::l))≤X')
include hp ha hq hx hG e
lemma spreadPaid : Weigh (rim F) X':=by
    intro x b u v hu hv
    let r:=sun G e; have hr:= sunny e; let i:=primary x e; let p':= (Exterior.coord b,e); let m(j:Primary n G):=separation (rope j).1 x.1
    have hW(j:Primary n G):m j≤ extent (Whisk.zone (Measuring.chart n G) ∅ [i,j]):=by
        change separation (ℓ j) (ℓ i) ≤ _; exact Whisk.curve (by simp [Whisk.zone]) (by simp [Whisk.zone])
    have ht:(∑ j:Primary n G,|Y [i,j]| *swipe ℓ a p [i,j])≤X':= hx i -- Yarn 1= ∑ j…
    have he : (∑ i:Site n,|M x (i,b) u v| *beadPad x.1 i 6)=_:=fair e x b (fun z=>|M x z u v| *beadPad x.1 z.1 6)
    rw [he]; refine le_trans (Finset.sum_le_sum fun j _=>?_ ) ht
    split; next hh=>
       have hj:j.2=e:= Prod.mk.inj hh|>.2
       have hh := norm_inner_le_norm (𝕜:=ℝ) u v; rw [hu,hv,mul_one] at hh
       refine mul_le_mul ?_ ?_ (by unfold beadPad; positivity) (abs_nonneg _)
       · rw [stream F i j h,hj,show rope i=x from curb ..,show i.2=e from rfl,Midpoint.blazing _ hG hp x (rope j) r hr u v,abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hh
       let d:=extent (Whisk.zone ℓ ∅ [i,j]); change (1+(m j:ℝ))^6 ≤ Measuring.factor a p d; unfold Measuring.factor
       exact ((pow_le_pow_left₀ (by positivity : 0 ≤ 1+(m j:ℝ)) (show 1+(m j:ℝ) ≤ 1+(d:ℝ) from by exact_mod_cast Nat.add_le_add_left (hW j) 1) _).trans (pow_le_pow_right₀ (by simp) hq)).trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))
    exact mul_nonneg (abs_nonneg _) (effect ..|>.le)
lemma candles (x:Primary n G)(s:Strand G) (L:List Axis)(hh:L.length <3) : |Measuring.parcel (target x) L s (fun l=>buoy F 0 (x::l)) []| ≤ 64*cost (rim F) (sun G e) X':=by
   let i:=rope x; let b:Axis:=Exterior.axisEquiv.symm s.1; let u:= sun G x.2; let v:=sun G s.2
   let w(L:List Axis)(j:Site n):= matry L (MultiNext.SignedSource.Pattern.xyz (lift (j-i.1))); let K':= cost (rim F) (sun G e) X'
   have ht: Measuring.parcel (target x) L s (fun l=>Y (x::l)) []= ∑ j:Site n,cell R i (j,b) u v*w L j:=by
       have hx : (∑ j:Site n,cell R i (j,b) u v*w L j)=_:=fair s.2 i b fun z=> cell R i z u v*w L z.1
       rw [hx]; unfold Measuring.parcel target; refine Finset.sum_congr rfl fun j _=> ?_; have hb:(Exterior.coord b,s.2)=s:= Prod.ext (Exterior.axisEquiv.apply_symm_apply s.1) rfl
       rw [hb]; split; next he=>
          change matry _ _*Y [x,j]=_; rw [stream F x j h,show j.2=s.2 from congr_arg Prod.snd he,mul_comm]; rfl
       next he=> rw [zero_mul]
   have hf(q:List Axis)(hv:q.length≤2): |raw R i b u v q|≤ 32*K':= bars i u v hG hp (spreadPaid F h hG e hp ha hq hx) (sunny ..) (sunny ..) (sun G e) (sunny ..) b q hv
   rw [ht]; have hk:0 ≤ K':=by have hh:0 ≤32*K':=(abs_nonneg _).trans (hf [] (by simp)); linarith
   have h(j:Site n)(k:Axis):MultiNext.SignedSource.Pattern.xyz (lift (j-i.1)) k=coord i.1 j k:=rfl
   cases L with
   | nil=> apply le_trans _ (hf [] (by simp)|>.trans (show 32*K' ≤ 64*K' from by linarith)); unfold raw w; simp [matry]
   | cons a l=>
      cases l with
      | nil=> apply le_trans _ (hf [a] (by simp)|>.trans (show 32*K' ≤ 64*K' from by linarith)); unfold raw w; simp [matry,h]
      | cons b' l=>
         simp only [List.length_cons] at hh; rw [show l=[] from by simpa using (show l.length=0 by omega)]
         have hx:=hf [a,b'] (by simp); have hz:=hf [a] (by simp); let c:ℝ:= if a=b' then 1 else 0; have hc:|c|≤1:=by unfold c; split <;> norm_num
         have hw(j: Site n):w [a,b'] j= coord i.1 j a*(coord i.1 j b' - c)/2:=by unfold w c; by_cases ha:b'=a; simp [ha,matry,h,YM.basis]; ring; simp [ha, Ne.symm ha,matry,h,YM.basis]; ring
         rw [show ∑ j:Site n, M i (j,b) u v*w [a,b'] j= (raw R i b u v [a,b']-c*raw R i b u v [a])/2 from ?_]; swap
         · unfold raw;rw [Finset.mul_sum, ←Finset.sum_sub_distrib,Finset.sum_div]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [hw]; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil]; ring
         rw [abs_div,abs_of_pos (by norm_num : 0 < (2:ℝ)),div_le_iff₀ zero_lt_two]; refine le_trans ((abs_sub ..).trans (add_le_add hx (?_:|c*raw R i b u v [a]|≤32*K'))) ?_
         · rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) hc).trans hz
         change _ ≤ 64*K'*2; linarith
end YM.MSbar.Lis
