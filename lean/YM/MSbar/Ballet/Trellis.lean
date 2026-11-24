import YM.MSbar.Ballet.EpochT
import YM.MSbar.Ballet.Tines
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Ballet
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Alto Mosaic Mosaic.Issue
variable {G:Gauge}
open Work.G05
variable {n:Side}{k p m q:ℕ}{B Y K R t:ℝ}{σ:Type}[Fintype σ][DecidableEq σ]{f g:Positions σ→ℝ}
local notation "Q"=>Positions σ
variable {J:Type}[Fintype J]{L:σ→ Site n}{G:Positions σ→ℝ}
variable (Z:J→Site n)(F:J→Positions σ→ℝ)(he:G=fun i=>∑ j,F j i)
     (hv: 1 ≤ Y)(ht:0 < t)(hr:t ≤ 1)(hY:t*Y <1)(hp:p+3  ≤ m)
     (hj:0≤B)(hn:∀ i:J,∀ x:Positions σ,‖x‖<1→Allows m (F i) x B)
open Metric
local notation "K!"=> closedBall (0: Q) Y
include hv ht hr hY hp hn hj
include he
local notation "Δ"=>starP t p G
lemma spray : (starP t p G)=fun i=>∑ j,starP t p (F j) i:=by
    have hh:Work.G05.blockTaylor (2+p) G=fun x=> ∑ j,blockTaylor (2+p) (F j) x:=Jade.tails (2+p) (fun j _=> (hn j 0 (norm_zero|>.trans_lt zero_lt_one)).1) (Eventually.of_forall fun i=> congr_fun he i)
    funext i; unfold starP; simp_rw [Pi.sub_apply]; rw [hh,← Finset.mul_sum,Finset.sum_sub_distrib,he]; -- rewriting he affects y.T. 
variable (hk:∀ i:J,F i ∘ haul σ (curbL L (Z i) k)=F i)[DecidableEq J] {N M U:ℕ}{a:ℝ}(ha:0≤a)(hz: a ≤ 1)(hS:Multiplicity Z M)(hk':Multiplicity L N)
local notation "u"=>fun i=> curbL L (Z i) k
local notation "K1"=>t^(p+1)*(B*Y^(p+3))
include ha hz hk hS hk'
open Finset
-- sum real weighted boom
lemma riches (q':ℕ)(h:q' < m): JetTab L a U Y (closedBall 0 Y) (starP t p G) q' (Y^(q'+1)* (cities M k*rugL 1 (t^(p+1)*(B*Y^(p+3))) U k q' (cities N k))):=by
    let K:=t^(p+1)*(B*Y^(p+3)); have hK:0 ≤ K:=by unfold K; positivity
    let V (i:J):=starP t p (F i); have hp'(i:J)(l:List σ)(hl:l.length=q'+1) (x:Q)(hx:x∈K!): |buoy (V i) x l| ≤ K:= scores F hv ht hr hY hp hj hn x hx l (by omega) i|>.1
    have hg(i:J)(x:Q)(hx:x∈K!):ContDiffAt ℝ m (V i) x:=scores F hv ht hr hY hp hj hn x hx [] (by simp) i|>.2
    let U0(i):= u i; let H(i:J)(l:List σ):ℝ:= CrossH.pulse (U0 i) l
    have hp''(i:J): V i ∘ haul σ (U0 i)= V i:=by
        funext x; let y:=U0 i; have hq: t • haul σ y x=haul σ y (t • x):=by funext j; unfold haul; simp only [Pi.smul_apply]; split<;> simp
        have hh0:= railQ (p:=2+p) (F i) t _ (hk i) ((hn i _ (norm_zero|>.trans_lt zero_lt_one)).1.of_le le_top)
        have hξ : F i (haul σ y (t • x))= F i (t • x):=congr_fun (hk i) _; have hθ:blockTaylor (2+p) (F i) (haul σ y (t • x))=blockTaylor (2+p) (F i) (t •x):=congr_fun hh0 _; unfold V starP; rw [Function.comp_apply,Pi.sub_apply,Pi.sub_apply,hq,hξ,hθ]
    let P(l:List σ):=Y^(q'+1)*(∑ i, H i l*K); have hp0(i:J)(l):0 ≤ H i l:= by unfold H CrossH.pulse; split <;> norm_num
    have hP(x:Q)(l:List σ)(hl:l.length=q'+1)(hx:x∈K!) : |buoy Δ x l|≤ ∑ i,H i l*K :=by
        rw [spray F he hv ht hr hY hp hj hn,buoy, Lis.tot m (List.map (@Uniform.bolt σ) l) Finset.univ (fun j=>starP t p (F j)) (fun i _=> hg i x hx) (by rw [List.length_map];omega)] -- @ fix.
        apply (Finset.abs_sum_le_sum_abs ..).trans; refine Finset.sum_le_sum (fun i _=>?_); unfold H CrossH.pulse; split; next h'=> rw [one_mul]; exact hp' i l hl x hx
        next he=> rw [zero_mul]; change |buoy (V i) x l| ≤ 0; rw [show buoy (V i) x l=0 by by_contra! hy'; exact he (subscriptions _ (hp'' i) (hg i) x hx _ hy' (by omega)),abs_zero]
    let U1:=liftW 1 U (2*k); have hU1:0≤ U1:=(wpos ..).le; let W:=rugL 1 K U k q' (cities N k); have hW:0≤ W:= mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (mul_nonneg hK hU1); have hB(x):0≤ Y^(x:ℕ):=by positivity
    refine ⟨mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) hW),P,(fun l hl=>⟨mul_nonneg (hB _) (sum_nonneg fun i _=> mul_nonneg (hp0 ..) hK),fun x hx=>(mul_comm ..).trans_le (mul_le_mul_of_nonneg_left (hP x l hl hx) (by positivity))⟩),fun i=>?_⟩ -- hx inference
    let B':= curbL Z (L i) k
    let M'(j:J):= if j∈B' then W else 0
    let f(j:J)(l:List σ):=H j (i::l)*K *swipe L a U (i::l)
    unfold P; rw [show (Yarn _ _ :ℝ)= Y^(q'+1)*∑ j,Yarn q' (f j) from ?_]; swap; · rw [←scarves,←sheen]; apply stitch; intro k hk; rw [mul_assoc,Finset.sum_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply le_trans (b:=∑ j: J,M' j) (Finset.sum_le_sum ?_) ?_; swap; · simp only [M', Finset.sum_ite_mem,Finset.sum_const,nsmul_eq_mul]; simp; gcongr; exact dressP _ hS _ _
    intro j hj; unfold M'; split
    next hx=>
       have hc : Yarn q' (f j) ≤ Yarn q' fun l:List σ=> CrossH.pulse (U0 j) l * (K * U1):=by
            apply shiny; intro l hl; unfold f H CrossH.pulse; split
            next h0=> rw [if_pos (fun a ha=>h0 a (List.mem_cons_of_mem _ ha)),one_mul,one_mul]; apply mul_le_mul_of_nonneg_left _ hK; apply le_trans ?_ (show liftW a U (2*k)≤ U1 from (by unfold U1 liftW; gcongr)) -- name
                      apply w_more _ ha; apply Whisk.yard; intro i' he j' hs
                      have hh(b:Site n)(hv:b∈Whisk.zone L ∅ (i::l)): separation b (Z j) ≤ k:=by obtain ⟨c,h₀,h⟩:= List.mem_map.mp (List.mem_toFinset.mp (show _ from (by simpa only [Whisk.zone,Finset.empty_union] using hv))); rw [← h]; exact Finset.mem_filter.mp (h0 c h₀)|>.2
                      exact (separation_triangle i' _ j').trans ((Nat.add_le_add (hh _ he) (le_trans (separation_comm ..|>.le) (hh _ hs))).trans_eq (by omega))
            next he=> split <;> simp <;> positivity
       refine hc.trans ?_; rw [poker,spooler]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr (dressP _ hk' _ _)) _) (mul_nonneg hK hU1)
    next hx=>
       refine le_trans ?_ (spool (ι:=σ) q'|>.le); apply shiny; intro l hl; unfold f H CrossH.pulse; rw [if_neg ?_,zero_mul,zero_mul]; intro he; apply hx; have hh:= Finset.mem_filter.mp (show i∈curbL L (Z j) k from he i (List.mem_cons_self ..)); exact Finset.mem_filter.mpr ⟨mem_univ _,le_trans (separation_comm ..|>.le) hh.2⟩
end YM.MSbar.Ballet
