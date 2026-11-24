import YM.WilsonCoeffUV.Winding.KernelSeed
/-! # The winding crossing with fixed-order rung. W fed only on
`inc n`, no deeper. `K` singular integral prices charged on actual supplying
slots; ample factors not numerically optimized. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Function Filter Lattice RG Embroider Soil Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent AnalyticNext.QuarticMatch.Sheets
open scoped Topology BigOperators
variable {n L:Side}{ι U X α β V:Type*}{G:Gauge}{i j k r e a:ℕ}{s A B t q :ℝ}
structure Arch (G:Gauge) where
    P : Patch
    K : KernelChoices
    R : ChartRatio G
    trees : P.Branches K G
    pay : LocalRatio R
    s : ℝ
    h : 0<s
    mass : ℝ
    book : 1 ≤ mass
namespace Arch
variable (C:Arch G)
abbrev peg n:= weaveFine (G:=G) (ratioN C.P.L n)
abbrev roll n:= weaveH (G:=G) (ratioN C.P.L n)
abbrev feather:= Larvae G C.P.L
abbrev dial:= Hinge G C.P.L
end Arch
structure ScrollV (e:ℕ)(C:Arch G) where
    n : Side
    W : Crude G
    T (j:Side): Matrix (Body 1 (j*C.P.L)) (Body 1 j) ℝ
    H : FaceRow
    Y : FaceRow
    Z : Bank.Canvas G
    γ : ropes Cover (C.feather) C.feather
    M : ropes Cover C.feather (Hooks G)
    lights : Rail (allotM (C.peg n) (Equiv.refl _) (teller G C.P C.K T n)) M C.s C.mass
    glow : Rail (allotM (C.peg n) (C.peg n) (mer (G:=G) C.P C.K H n)) γ C.s C.mass
    guide : Rail (precisionC G n Y) (plain G Y) C.s C.mass
    coin:ℝ
    paid :1≤coin
    fare (i:ℕ) (v:i≤ e)(r:ℕ): Sight (W (n*C.P.L) i r) (Z i r) C.s coin
namespace ScrollV
variable {C:Arch G}(p:ScrollV e C)
abbrev wheel:=stepAt C.P C.K p.n
abbrev shadow:= xree C.P C.K p.n
abbrev rampU:=stair (upper (β:=Hooks G) (allotM (C.peg p.n) (C.peg p.n) (mer (G:=G) C.P C.K p.H p.n)) 0) (β:=Hooks G) 0
abbrev landing:= stair (upper (β:=Hooks G) p.γ 0) (β:=Hooks G) 0
abbrev W':= p.W (p.n*C.P.L)
abbrev cone:=teller G C.P C.K p.T p.n
abbrev archCold (i):=bend (C.roll p.n) (casePW p.wheel C.R p.cone p.W' i)
abbrev archCover:= stellar C.P C.K C.R p.M p.Z
abbrev vault (h i):= bend (C.roll p.n) (xray p.wheel p.shadow p.H (p.T p.n) C.R p.W' h i)
abbrev coverVault:= spurs C.P C.K C.R p.γ p.M p.Z
abbrev shipped:= summer p.wheel p.shadow p.H (p.T p.n) C.R p.W'
abbrev trimmed:=snow C.P C.K C.R p.γ p.M p.Z
abbrev player:= winter p.wheel p.shadow p.H p.Y (p.T p.n) C.R p.W'
abbrev plume:=tinge C.P C.K C.R (plain G p.Y) p.γ p.M p.Z
lemma vaultTip (h i):p.vault h i=abr p.rampU p.archCold h i:=whyPack ..
lemma rateRamp : Rail p.rampU p.landing C.s C.mass:= by
    have hp:=zero_le_one.trans C.book; exact (p.glow.upperL (Rail.zero.more hp)).stairL (Rail.zero.more hp)
end ScrollV
lemma priceMP (α:Type*) [Fintype α](r:ℕ){s:ℝ}(p:0<s):0≤ priceM α r s:=by
   apply add_nonneg; · cases r with
                        | zero=> rw [tiePay,pow_zero]; norm_num
                        | succ r=> exact pow_nonneg (boardPay_nn (div_pos (by linarith) (by positivity))) _
   exact mul_nonneg (by norm_num) (pow_nonneg (boardPay_nn (tail_good _ (by positivity))) _)
lemma glass_charge [Fintype α](b:ℕ)(h:0<s)(p:0≤A):0 ≤ glassC (α:=α) b s A :=by unfold glassC; split; exact zero_le_one; exact mul_nonneg (mul_nonneg (priceMP _ _ h) (by positivity)) (pow_nonneg p _)

-- widths post: `light(k)` collected from every Arrow, e,k finite. Does not iterate.
variable {T:Arch G→Type}
abbrev CloseK (T: Arch G→Type)(e r:ℕ):= (I:Arch G)→(p:ScrollV e I)→ Ten ℝ (Co p.n (T I)) r
abbrev RoofK (T:Arch G→Type)(e r:ℕ):= (I:Arch G)→(p:ScrollV e I)→ Ten ℝ (Cloth (T I)) r
def Layered (P:CloseK T e r)(F:RoofK T e r): Prop:= ∃ d:ℕ,∀ I,∃ s C:ℝ,0<s∧ 0≤C∧∀ p,Sight (P I p) (F I p) s (C*p.coin^d)
variable {P Q:CloseK T e r}{F H:RoofK T e r}
lemma Layered.add (h:Layered P F)(p:Layered Q H): Layered (fun I u=> P I u+Q I u) (fun I u=>F I u+H I u):=by
   obtain ⟨d,H'⟩:=h; obtain ⟨c,V⟩:=p; refine ⟨max c d,fun I=>?_⟩; obtain ⟨s,A,b,e,g⟩:=H' I; obtain ⟨t,B,f,w,x⟩:=V I; refine ⟨min s t,A+B,lt_min b f,add_nonneg e w,fun p=>?_⟩; rw [add_mul]; exact ((g p).mono (min_le_left ..) |>.more (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ p.paid (le_max_right c d)) e)).add (((x p).mono (min_le_right ..)).more (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ p.paid (le_max_left c d)) w))
lemma Layered.zero: Layered (T:=T) (fun _ (_:ScrollV e _)=> (0:Ten ℝ _ r)) 0:=⟨0,fun I=>⟨1,0,one_pos,le_rfl,fun p=> Sight.zero.more (by simp)⟩⟩
lemma Layered.μ (h:Layered P F)(w:Arch G→ℝ): Layered (fun i p=>w i• P i p) (fun i p=>w i • F i p):=by
   obtain ⟨d,H⟩:= h; refine ⟨d,fun I=>?_⟩; obtain ⟨s,a,ht,hA,V⟩:=H I; refine ⟨s,‖w I‖*a,ht,mul_nonneg (norm_nonneg _) hA,fun p=> ?_⟩; rw [mul_assoc]; exact (V p).μ _
lemma Layered.sub (h:Layered P F)(p:Layered Q H): Layered (fun i p=>P i p-Q i p) (fun i p=>F i p-H i p):=by simpa only [sub_eq_add_neg,neg_one_smul] using h.add (p.μ fun _=>-1)
lemma Layered.sum {S:Finset ι}{P:ι→CloseK T e r}{F:ι→RoofK T e r} (h:∀ i∈ S,Layered (P i) (F i)): Layered (fun I p=>∑ i∈ S,P i I p) (fun I p=>∑ i∈ S,F i I p):=by
   classical
   induction S using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact Layered.zero
   | @insert i S hi ih=> simp_rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).add (ih (fun i v=> h i (Finset.mem_insert_of_mem v)))

lemma bankPrep (G:Gauge)(e i r:ℕ)(p:i≤ e): Layered (T:=Arch.dial) (fun (I:Arch G) (p:ScrollV e I)=> p.archCold i r) (fun _ p=>p.archCover i r):=by
    refine ⟨1,fun I=>?_⟩; obtain ⟨A,g⟩:= meterSun I.pay i r I.s I.h; let t:= I.s/8; have hT:0<t:=div_pos I.h (by positivity); have hx:t≤ I.s:=by unfold t; linarith [I.h]
    obtain ⟨B,f⟩:= meterZen I.trees i r t hT; have hA:= (g 1).aim.1; have hB:= (f 1).aim.1
    let L:=I.P.L; let K:=Real.exp (16*I.s)*Fintype.card (Site L); have hK:0≤ K:=by unfold K; positivity
    let u:=glassC (α:=I.feather) r t I.mass; let v:=glassC (α:=I.dial) r t I.mass; set C:=u*(2*A*K)+v*B
    have he:= I.book; have hu:= glass_charge (α:=I.feather) r hT (zero_le_one.trans he); have hv:=glass_charge (α:=I.dial) r hT (zero_le_one.trans he); have hu':0≤u:=hu; have hv':0≤v:=hv; have hc:0≤ C:=by unfold C; positivity
    refine ⟨t/32,C+2*u*K,div_pos hT (by positivity),by positivity,fun q=>?_⟩; dsimp only; rw [show q.archCold i = _ from (stellar_pack (P:=I.P) I.K I.R q.W (teller G I.P I.K q.T) q.n i)]
    let M:= allotM (I.peg q.n) (Equiv.refl _) q.cone; have hh: Rail (upper 1 M) (upper 1 q.M) t I.mass:= by exact (Rail.unit.more he).upperL (q.lights.mono hx)
    have hb: Sight (scrub (fun i=>bend (I.roll q.n) (sprig (jointPen G q.wheel) 2 i)) i r) (scrub (warren I.P I.K G) i r) t B:=by unfold scrub; split; exact Sight.zero.more hB; exact f q.n
    have hg: Sight (scrub (q.W') i r) (scrub q.Z i r) I.s q.coin:=by unfold scrub; split; exact Sight.zero.more (zero_le_one.trans q.paid); exact q.fare _ p r
    let X:= (g (q.n*L)).panelCost (L:=L) I.h
    have hX:= ((SiteW.glass hh (F:=plants L (bearingJ I.R i)) (Q:=bend (I.peg q.n) (sprig (unhaar I.R) 0 i)) X hT).sub (SiteW.glass (hh.stairL (Rail.ladderL.more he)) (F:=scrub _ i) (Q:=scrub _ i) hb hT)).sub (SiteW.glass hh (F:=plants L (scrub q.Z i)) (Q:=bend (I.peg q.n) (scrub q.W' i)) (hg.panelCost I.h) hT)
    apply hX.more; rw [pow_one]; change u*(2*A* _*Fintype.card (Site L))+v*B+ u*(2*q.coin*_*Fintype.card (Site L))≤ _
    rw [show _+v*B=C from by unfold C K; ring, show u*(2*q.coin*Real.exp _*Fintype.card (Site L))= (2*u*K)*q.coin from by unfold K; ring,add_mul]; exact add_le_add (le_mul_of_one_le_right hc q.paid) le_rfl
section
variable {S: (I:Arch G) → (p:ScrollV e I) → Gen ℝ (Co p.n I.dial)}{F: (I:Arch G)→ (p:ScrollV e I) → Gen ℝ (Cloth I.dial)}
lemma Layered.light (h:Layered (T:=Arch.dial) (fun i p=>S i p (r+2)) (fun i p=> F i p (r+2))): Layered (T:=Arch.dial) (fun i p=>ripple p.rampU (S i p) r) (fun i p=> crimp p.landing (F i p) r):=by
   obtain ⟨d,H⟩:=h; refine ⟨d,fun I=>?_⟩; obtain ⟨s,b,hs,hb,V⟩:= H I; set t:=min s I.s; have hx:0<t:= lt_min hs I.h; set u:=priceM I.dial 2 t; have hu:=priceMP I.dial 2 hx; have hh:=zero_le_one.trans I.book
   have he:0≤ u:=hu
   refine ⟨t/32,u*(ore r (r+1)*2*I.mass*b),div_pos hx (by norm_num),by unfold ore; positivity,fun p=>?_⟩; dsimp only; rw [← Bank.rain_reads]; exact (SiteW.worthy (SiteW.rainL (F:= F I p) (Q:= S I p) (p.rateRamp.mono (min_le_right s _)) ((V p).mono (min_le_left ..)) hx.le) hx).more (le_of_eq (by unfold u; ring))
variable {S':(I:Arch G)→(p: ScrollV e I)→Gen ℝ (Co p.n I.dial)}{Z:(I:Arch G)→(p:ScrollV e I)→Gen ℝ (Cloth I.dial)}
lemma Layered.fletch (h:Layered (T:=Arch.dial) (fun i' p=> S i' p (i+1)) (fun i' p=> F i' p (i+1)))(g:Layered (T:=Arch.dial) (fun i p=>S' i p (j+1)) (fun i p=> Z i p (j+1)))(p:i+j=r): Layered (T:=Arch.dial) (fun k p=> wear (swivel (rill p.rampU (S k p) (S' k p) r i j))) (fun k p=> worn (swivel (rill p.landing (F k p) (Z k p) r i j))):=by
   subst r; obtain ⟨d,H⟩:=h; obtain ⟨c,V⟩:=g; refine ⟨d+c,fun I=> ?_⟩; obtain ⟨s,b,x,y,H⟩:=H I; obtain ⟨t,a,f,g,V⟩:=V I; let z:= min I.s (min s t); have hx:0<z:= lt_min I.h (lt_min x f); let u:= priceM I.dial 2 z; have hu:0≤u:= priceMP I.dial 2 hx
   have hz:=zero_le_one.trans I.book; have hh:z≤min s t:= min_le_right ..; refine ⟨z/32,u*(ore i j*3*I.mass*b*a),div_pos hx (by norm_num),by unfold ore; positivity,fun p=>?_⟩; apply (SiteW.worthy (SiteW.rillL (Z:=S I p) (Y:=F I p) (Q:=S' I p) (F:=Z I p) (p.rateRamp.mono (min_le_left ..)) ((H p).mono (hh.trans (min_le_left ..))) ((V p).mono (hh.trans (min_le_right ..))) hx.le |>.spin) hx).more; unfold u; rw [pow_add]; exact le_of_eq (by ring)
end
lemma Layered.snowLight (G:Gauge)(i j k r)(h:i≤ k): Layered (T:=Arch.dial) (fun (I:Arch G) (p:ScrollV k I)=>p.vault j i r) (fun _ p=> p.coverVault j i r) := by
   simp_rw [ScrollV.vaultTip]; induction j using Nat.strong_induction_on generalizing i r with
   | h j ih=>
       cases j with
       | zero=> simp_rw [abr_zero,ScrollV.coverVault, spurs,tide_zero]; exact bankPrep G k i r h
       | succ j=>
            simp_rw [abr_next,ScrollV.coverVault,spurs,tide_rise,Pi.smul_apply,Pi.add_apply]; apply Layered.μ (w:=fun _=>_); apply Layered.add; · exact (ih j j.lt_succ_self i (r+2) h).light (S:=fun I p=>abr p.rampU p.archCold j i) (F:=fun I p=>p.coverVault j i)
            unfold ravel curlJ; simp_rw [Finset.sum_apply]; apply Layered.sum; intro y hy; have hv:= Finset.mem_antidiagonal.mp hy; apply Layered.sum; intro z hz; have hU:= Finset.mem_antidiagonal.mp hz; simp_rw [← rill_reads, whittle]; apply Layered.sum; intro w v; apply Layered.fletch (S:= fun I p=>abr p.rampU p.archCold y.1 z.1) (F:=fun I p=>p.coverVault y.1 z.1) (S':=fun I p=>abr p.rampU p.archCold y.2 z.2) (Z:=fun I p=>p.coverVault y.2 z.2) _ _ (Finset.mem_antidiagonal.mp v)
            · exact ih _ (by omega) _ _ (by omega)
            exact ih _ (by omega) _ _ (by omega)
lemma Sight.scoop {P:Ten ℝ (Co n (α⊕β)) r}{F:Ten ℝ (Cloth (α⊕β)) r}(h:Sight P F s A): Sight (scoop P) (scoop F) s A:=by
    have he: pruce (Bank.scoop P)=Bank.scoop (pruce P):=by by_cases p:r=0 <;> simp only [pruce,p,↓reduceIte]; rfl
    refine ⟨by rw [he]; exact scrapC h.aim,scrapC h.bound,⟨h.bound.1,fun x v=>?_⟩,fun b x=>h.strollT b (pierR ∘ x)⟩; rw [he]; exact h.gall.local_w (pierR ∘ x) v
lemma Layered.shimmer (G:Gauge)(e i r)(h:i ≤ e): Layered (T:=fun _=>Hooks G) (fun (I:Arch G) (p:ScrollV e I)=> p.shipped i r) (fun _ p=> p.trimmed i r):=by
   let S:= Finset.range (3+3*i)
   obtain ⟨d,H⟩:= Layered.sum (S:=S) (fun j _=>Layered.snowLight G i j e r h)
   refine ⟨d,fun I=>?_⟩; obtain ⟨s,b,c,d,H⟩:= H I; refine ⟨s,b,c,d,fun p=>?_⟩; dsimp only; rw [show p.shipped i=sluice (∑ j∈ S,p.vault j i) from season_fold I.P I.K I.R p.H _ _ _ i, sluice,Finset.sum_apply]; unfold ScrollV.trimmed snow; rw [sluice,Finset.sum_apply]; exact (H p).scoop
lemma skyZ (W:PowerSeries ℝ)(s:ℝ)(k r): Sight (uband (U:=Co n α) (Fintype.card (Site n) • W) k r) (uband (U:=Cloth α) W k r) s (‖PowerSeries.coeff k W‖) :=by
    cases r with
    | zero=>
        have he v: pruce (uband (U:=Co n α) (Fintype.card (Site n) • W) k 0) v=PowerSeries.coeff k W:= by
          simp only [pruce,↓reduceIte, uband,Pi.smul_apply,shine_lit]; rw [map_nsmul,nsmul_eq_mul,smul_eq_mul,inv_mul_cancel_left₀ (show (Fintype.card (Site n):ℝ)≠0 by positivity)]
        refine ⟨⟨norm_nonneg _,fun x=>?_⟩,⟨norm_nonneg _,fun x=>?_⟩,⟨norm_nonneg _,fun x v=>?_⟩,fun _ _=> rfl⟩
        · rw [he]; simp [soar,league]
        · rw [uband,shine_lit]; simp [soar,league]
        rw [he]; change ‖PowerSeries.coeff _ _- PowerSeries.coeff _ _‖≤_; rw [sub_self,norm_zero]; exact mul_nonneg (norm_nonneg _) (catch_hot ..)
    | succ r=> rw [uband,uband,shine_dark (show 0≠r+1 from by omega),shine_dark (show 0≠r+1 from by omega)]; exact Sight.zero.more (norm_nonneg _)
theorem windingVault (G:Gauge)(e i r)(p:i ≤ e): Layered (T:=fun _=>Hooks G) (fun (I:Arch G) (p:ScrollV e I)=> p.player i r) (fun _ p=> p.plume i r):=by
    refine Layered.add (Q:=fun I (p:ScrollV e I)=>uband (U:= Co p.n (Hooks G)) (plugζ p.wheel I.R) i r) (H:=fun I (p:ScrollV e I)=>uband (U:=Cloth (Hooks G)) (perζ I.K I.R) i r) (Layered.sub (P:=fun I (p:ScrollV e I)=> flatPal (precisionC G p.n p.Y) i r) (F:=fun I p=>flatPal (plain G p.Y) i r) ?_ (Layered.shimmer G e i r p)) ?_
    · refine ⟨0,fun I=>⟨I.s,I.mass,I.h,zero_le_one.trans I.book,fun p=> ?_⟩⟩; dsimp only; rw [flatPal,flatPal,pow_zero,mul_one]; split; swap; · exact Sight.zero.more (zero_le_one.trans I.book)
      by_cases h:2=r; · subst r; simp_rw [shine_lit]; exact p.guide.bruise
      simp_rw [shine_dark h]; exact Sight.zero.more (zero_le_one.trans I.book)
    let P (I:Arch G)(p:ScrollV e I):= uband (U:=Co p.n (Hooks G)) (plugζ p.wheel I.R) i r
    change Layered P (fun I p=>uband (U:=Cloth (Hooks G)) (perζ I.K I.R) i r)
    refine ⟨0,fun I=>⟨I.s,‖PowerSeries.coeff i (perζ I.K I.R)‖,I.h,norm_nonneg _,fun p=>?_⟩⟩; unfold P ScrollV.wheel; rw [plug_site,pow_zero,mul_one]; exact skyZ _ _ _ _
end YM.WilsonCoeffUV.Winding
