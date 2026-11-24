import YM.FormalBulk08.Avenue.Orbit
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
open Flat UVExtension.Free
variable {G:Gauge}
open Reef Mesa Gorge

variable {D l:ℕ}
open Kemp Pose Dawn Spigot Orb Wick Series Jets MeasureTheory Lotus Shore Lava Rift
open Grail
-- exact Kalm & cream for any test mark at leading
open City PowerSeries
open Roof Wine Source Source.Drops Labels
variable {o:Loc G 1} {d:ℕ}
open Trellis Aster Dove Quire Clover Elm North
open Dove.Lab
variable {I:Type}{K:KernelChoices}{W:Lab G K I}
open Spruce
variable {P:Page I}{C:Pin P}{τ:Time I}{Q:Deck C→ℝ}
lemma liquid_clock {f:I→ℝ} {L:Turn C→ℝ}(h:∀ i:Turn C,|Q i.ups|≤|Q i.bed|+ |L i|)(ht:Faint τ f (fun i=> Q (startP i C)))(hp: Faint (qday τ C) (fun i=> f i.a) L)(hb:Soft τ (fun i=>(steps C i:ℝ)))(he:∀ i, 0≤f i): Faint (rday τ C) (fun i=> f i.a) Q:= by
   let U (i:Deck C):= max 0 (|Q i|-|Q (startP i.a C)|)
   have hv (i:Turn C) : |U i.ups|≤ |U i.bed|+ |L i|:= by
       rw [abs_of_nonneg (show 0≤U i.ups from le_max_left ..),abs_of_nonneg (show 0≤U i.bed from le_max_left ..)]; unfold U; apply max_le (add_nonneg (le_max_left ..) (abs_nonneg _))
       have hx:=h i; have hp : i.ups.a=i.bed.a:=rfl;rw [hp]; linarith [le_max_right (0:ℝ) (|Q i.bed|- |Q (startP i.bed.a C)|)]
   have hh:= tinmoon (τ:=τ) (k:=fun (i:Deck C)=> f i.a) (T:=U) (fun i=>he _) (fun i=> le_rfl) hp hb (fun i=>by unfold U; simp
    ) hv
   refine (hh.plus ((ht.lower (g:=fun i=> |Q (startP i C)|) (fun _=>by rw [abs_abs])).link (fun i:Deck C=>i.a))).lower ?_; intro i; rw [abs_of_nonneg (add_nonneg (show 0≤U i from le_max_left ..) (abs_nonneg _))]; exact (sub_le_iff_le_add.mp (le_max_right ..))
lemma faint_forward {f:I→ℝ}{V:Type}[Fintype V][DecidableEq V]{Q:Deck C→ V→ℝ}{T:Turn C→ Matrix V V ℝ} {s w:V→ℕ}{b: Turn C→ V→ℝ}(h:∀ x:Turn C,Q x.ups=T x*ᵥ Q x.bed)(ht:∀ x,Found s w (tag (T x)) (b x))(hk:∀ j, Faint τ f (fun x=> Q (startP x C) j))(hp:∀ i j,Soft (qday τ C) (fun x=>T x i j))(hs:∀ i j,b i j≤1)(hz:∀ x,0≤ f x)(hb:Soft τ (fun i=>(steps C i:ℝ)))(j:V): Faint (rday τ C) (fun i=> f i.a) (fun i=> Q i j):= by
    let π:= priority s w;let B:=∑ i,π i;have hB i:π i ≤ B:= Finset.single_le_sum (f:=π) (fun i _=>Nat.zero_le _) (Finset.mem_univ _); generalize hP:B-π j=n; induction n using Nat.strong_induction_on generalizing j with
    | _ n ih=>
       let K(x:Turn C)(i:V):= Q x.bed i*T x j i; let Y: Finset V:=Finset.univ.erase j
       have hv x:Q (x:Turn C).ups j=Q x.bed j* b x j+ (∑ i∈Y,K x i):= by rw [h x]; unfold Matrix.mulVec dotProduct; unfold Y; rw [←Finset.add_sum_erase (Finset.univ:Finset V) (fun i=> (T x j i) * Q x.bed i) (Finset.mem_univ j)]; rw [show T x j j=b x j from (coeff_zero_C _).symm.trans ((ht x).due j),mul_comm (b x j)]; congr 1; exact Finset.sum_congr rfl fun i _=>mul_comm ..
       refine liquid_clock (fun i=> le_trans (le_of_eq (congr_arg abs (hv i))) ((abs_add_le ..).trans (?_))) (hk j) (faint_sums Y (f:=fun i x=>K x i) ?_) hb hz
       swap
       · intro i hi; by_cases hK:π j< π i; swap
         · have hs (x: Turn C) : K x i=0:= by unfold K; rw [show T x j i=0 from ?_,mul_zero]; by_contra h'; apply hK; exact promotes ((ht x).min j i (by change coeff 0 (PowerSeries.C _ )≠0;rw [coeff_zero_C];exact h') (Ne.symm (Finset.ne_of_mem_erase hi)))
           simp_rw [hs]; exact faint_zero ..
         exact ((ih (B-π i) (by have ht:=hB i;omega) i rfl).link (fun i:Turn C=> i.bed)).times (hp j i) -- time
       rw [abs_mul]; exact add_le_add_left (mul_le_of_le_one_right (abs_nonneg _) (by rw [abs_of_pos ((ht i).scale _)]; exact hs i j)) _
variable {F:Frame G d}
lemma nc_stamp (T:Tilework F)(b)(h:Colfax (Pose.slots F) (Pose.weight F) T b): Found (Pose.slots F) (Pose.weight F) (tag (noncontract F T)) b:= by
    refine ⟨fun i j he=>?_,h.paid,fun i j he hx=>?_⟩
    · have hp:noncontract F T i j=0:= if_neg (Ne.symm (Nat.ne_of_lt he)); change coeff 0 (PowerSeries.C _)=0; rw [coeff_zero_C,hp]
    change coeff 0 (PowerSeries.C _)=_; rw [coeff_zero_C,show noncontract F T i j= _ from (if_pos he:noncontract F T i j=coeff 0 (T i j)),h.diagonal i j he hx]
lemma nc_invoice {T:Turn C→Tilework F}{b:Turn C→Letter F→ℝ} (p:∀ i j,Soft (qday τ C) (fun x=>coeff 0 (T x i j)))(hp:∀ i, Found (slots F) (Pose.weight F) (tag (noncontract F (T i))) (b i))(hs:∀ i j, 1 ≤ b i j)(i j): Soft (qday τ C) (fun x=>(noncontract F (T x))⁻¹ i j):= by
    let A x:=tag (noncontract F (T x)); have h i j: Priced (qday τ C) (fun _=>1) (fun x=> A x i j) (fun x=>A x i j) 0:= by
       intro k hk; have hx:k=0:=by omega
       rw [hx]; apply Pact.constant; unfold A; have he x:coeff 0 (tag (noncontract F (T x)) i j)= _ := (show coeff 0 _ = noncontract F (T x) i j from coeff_zero_C (noncontract F (T x) i j)); simp only [he]; by_cases ht:Pose.slots F i=Pose.slots F j;swap; · unfold noncontract; simp_rw [if_neg ht]; exact soft_coin _ _
       unfold noncontract; simp_rw [if_pos ht]; exact p i j
    have ht:= (prize_back hp hp (?_) h i j 0 le_rfl).left; simp_rw [←(tagBack (hp _)).2] at ht; simp only [tag,RingHom.mapMatrix_apply,Matrix.map_apply,coeff_zero_C] at ht; exact ht
    intro k; apply (soft_coin (qday τ C) 1).below;intro x; have hx:= hs x k; rw [abs_one,abs_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ hx
end YM.FormalBulk08.Avenue
