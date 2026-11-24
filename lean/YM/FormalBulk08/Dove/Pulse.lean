import YM.FormalBulk08.Dove.Rubric

/-! Krpin. Example ages and test segments. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dove
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster PowerSeries
open scoped Topology ENNReal BigOperators Classical
variable {Z I:Type}{s:Z→ℕ}{τ:Time Z}{δ:Z→ℝ}{G:Gauge}{K:KernelChoices}{E:ℕ}{ρ:ChartRatio G}{W: Lab G K I}
namespace Lab.Voyage
variable (F:Voyage W s)(u:Use W ρ E)(v:LocalRatio ρ)(a:hue G)(hs:G.Simple) (p:Soft τ (fun z=> (chron _).day (F.bed z)))(h: Soft τ (fun i=> sowing (W.V (F.bed i).a).S (F.bed i).b ((F.bed i).b+s i)))
lemma skirt (U:ℕ→Pence)(i k j:ℕ)(he:j≤k): slopes U (i+k) j=expanse U (i+k) (i+k-j) := by rw [expanses_slopes _ _ _ (by omega), show i+k-(i+k-j)=j by omega]
lemma spire (U:ℕ→Pence)(i j:ℕ): spires U i j=expanse U i (i+j) := by rw [expanses_spires _ _ _ (by omega), show i+j-i=j by omega]
include u v a hs p h
lemma kingdom :
     let S:= spine F ρ a F.summit
     let T:= spine F ρ a F.top
     Priced (tbook τ s) (fun i=> F.Dend i.z) (fun i=> expanse (S i.z) (F.bed i.z).b ((F.bed i.z).b+i.i)) (fun i=> expanse (T i.z) (F.bed i.z).b ((F.bed i.z).b+i.i)) E ∧
     Priced (tbook τ s) (fun i=> F.Dend i.z) (fun i=>expanse (S i.z) ((F.bed i.z).b + s i.z) ((F.bed i.z).b+s i.z-i.i)) (fun i=>expanse (T i.z) ((F.bed i.z).b+s i.z) ((F.bed i.z).b+s i.z-i.i)) E := by
    obtain ⟨w,X,Y⟩:= runway u F τ p h; let S1:= fun i:transferPoint W=> bandK ρ a W (fun _=>i.top) i.a i.b;let T1:= fun i:transferPoint W=> bandK ρ a W (fun _=>i.summit) i.a i.b; obtain Q := hear u v hs a; have hD z:0≤F.Dend z:= (ratioR_pos ..).le
    have hv (i: Walk s): spinR targetPower (F.ridge i) ≤ Dend F i.z:= ratio_test F _ _ (by have :=i.away;omega) (by have :=i.away;omega)
    have hh (i: Walk s): spinR targetPower (F.slide i) ≤ Dend F i.z:= ratio_test F _ _ (by have :=i.away;omega) (by have :=i.away;omega)
    have hX: Priced (tcash τ s) (fun i=>Dend F i.z) (fun i=> bookH (S1 (F.ridge i))) (fun i=> bookH (T1 (F.ridge i))) E:= by
        have he(i:transferPoint W): Fresh (S1 i):=(pesto v a hs i i.top i.wing).1; have ht(i: transferPoint W): Fresh (T1 i):= (pesto v a hs i i.summit (i.wing.trans_le i.extra)).1; exact fun j hj=> Pact_lift (g:=F.ridge) X ((Q.goods he ht).1 j hj) hv
    have hy: Priced (tcash τ s) (fun i=> Dend F i.z) (fun i=> nextU (S1 (F.slide i))) (fun i=> nextU (T1 (F.slide i))) E:= by
        have he(i:transferPoint W): Fresh (S1 i):=(pesto v a hs i i.top i.wing).1; have ht(i:transferPoint W): Fresh (T1 i):=(pesto v a hs i i.summit (i.wing.trans_le i.extra)).1; exact fun j hj=> Pact_lift (g:=F.slide) Y (Q.next he ht j hj) hh
    intro S T; let f i:= (F.bed i).b; let g(i: Z):= (F.bed i).b+s i
    constructor
    · simp_rw [←spire]; exact rolls (S:=fun x j=>bookH (S x (f x+j))) (V:=fun x j=> bookH (T x (f x+j))) (T:=fun x=>spires (S x) (f x)) (U:=fun x=> spires (T x) (f x)) (fun i=> by rw [spires]) (fun i=>by rw [spires]) w hD (fun _=> book_fresh _) (fun _=>book_fresh _) (show Priced _ _ _ _ _ from Priced.constant τ _ 1 E) hX
    have hp(X:Z→ℕ→Pence): (fun i:Lengths s=> expanse (X i.z) ((F.bed i.z).b+s i.z) ((F.bed i.z).b+s i.z-i.i))=(fun i=>slopes (X i.z) (g i.z) i.i):= funext fun i=>(skirt _ _ _ _ i.endD).symm
    rw [hp,hp];exact rolls (T:=fun x=> slopes (S x) (g x)) (U:=fun x=> slopes (T x) (g x)) (S:=fun x i=> nextU (S x (g x-(i+1)))) (V:=fun x i=> nextU (T x (g x-(i+1)))) (fun i=>by rw [slopes]) (fun i=>by rw [slopes]) w hD (fun _=>fresh_N _) (fun _=>fresh_N _) (Priced.constant τ _ 1 E) hy
end Lab.Voyage
-- example hours. `scale` unshifted. Covers stated calendars along width selector h`
def logtime (K:Schedule)(j:ℕ)(w:ℝ)(h:0≤w):Time ℕ:= ⟨fun i=>2+w+|K.scale i-K.scale j|,fun i=>by linarith [abs_nonneg (K.scale i-K.scale j)]⟩
lemma dawn (P:Page Z)(j:Z→ℕ)(w:Z→ℝ)(h:∀ x,0≤ w x)(he:∀ x,P.age x=logtime (P.mesh x) (j x) (w x) (h x))(hz:Soft (chron P) (fun i=> (wideA i:ℝ))): Years P:= by
    refine ⟨⟨1,zero_le_one,fun x n i _ h'=>?_⟩,hz⟩; let S:=P.mesh x; rw [he]; change 2+w x+ |S.scale n-S.scale _| ≤ 1*(2+w x+ |S.scale i-S.scale _| + _);have hh : |S.scale n-S.scale (j x)|≤ sowing S i n + |S.scale i-S.scale (j x)|:= by
        nth_rw 1 [show S.scale n -S.scale (j x)=sowing S i n + (S.scale i-S.scale (j x)) by unfold sowing;ring]; exact (abs_add_le ..).trans_eq (by rw [abs_of_nonneg (sowing_plus S h')])
    rw [one_mul]; exact (add_le_add_right hh _).trans_eq (by unfold S;simp [add_comm,add_assoc])
-- typical pair costs prepaid with τ=t_k.age(coarser/finer index)
lemma daylight (F:Lab.Voyage (W:=W) s)(τ:Time Z)(he:∀ i,0≤δ i) (p:∀ i, let x:= F.bed i;(W.years x.a)=logtime (W.V x.a).S x.b (δ i) (he i))(h:∀ i, (W.years (F.bed i).a).day ((F.bed i).b+s i)=τ.day i): Soft τ (fun i=>(chron _).day (F.bed i))∧Soft τ (fun i=>sowing (W.V (F.bed i).a).S (F.bed i).b ((F.bed i).b+s i)) := by
    have H i: let D:= W.V (F.bed i).a; let S := D.S; let F':= (F.bed i); let q:= sowing S F'.b (F'.b+s i); 0≤q∧τ.day i=2+δ i+q ∧ (chron _).day F'=2+δ i:= by
        intro D S F' q; have hq:0≤q:=sowing_plus S (Nat.le_add_right ..); refine ⟨hq,?_ ,?_⟩
        · rw [←h,p]; change 2+δ i +|q| = _;rw [abs_of_nonneg hq]
        change (W.years (F.bed i).a).day _= _; rw [p]; simp [logtime,F']
    refine ⟨(soft_day _).below fun i=>?_, (soft_day _).below fun i=>?_⟩
    · rw [(H i).2.1,(H i).2.2]; exact (abs_of_nonneg (by have :=he i;linarith : 0≤ 2+δ i)).le.trans ((le_add_of_nonneg_right (H i).1).trans (le_abs_self _))
    rw [abs_of_nonneg (H i).1,(H i).2.1]; exact (le_add_of_nonneg_left (show 0≤ 2+δ i by have :=he i;linarith)).trans (le_abs_self _)
lemma dusk (F:Lab.Voyage (W:=W) s)(τ:Time Z)(he:∀ i,0≤δ i)(p:∀ i, let x:=F.bed i;W.years x.a=logtime (W.V x.a).S (x.b+s i) (δ i) (he i))(h:∀ i,(W.years (F.bed i).a).day (F.bed i).b=τ.day i): Soft τ (fun i=> (chron _).day (F.bed i)) ∧ Soft τ (fun i=> sowing (W.V (F.bed i).a).S (F.bed i).b ((F.bed i).b+s i)) := by
    refine ⟨?_, (soft_day τ).below fun i=> ?_⟩
    · convert soft_day τ using 1; funext i;exact h i
    let F':=F.bed i; let q := sowing (W.V F'.a).S F'.b (F'.b+s i); have hq:0≤q:=sowing_plus _ (Nat.le_add_right ..); rw [←h i,p i]; change abs q ≤ abs (2+δ i + abs ((W.V F'.a).S.scale F'.b-(W.V F'.a).S.scale (F'.b + s i)));rw [abs_sub_comm];change |q| ≤ abs (2+δ i + abs q); rw [abs_of_nonneg hq,abs_of_nonneg]; all_goals have :=he i; linarith
end YM.FormalBulk08.Dove
