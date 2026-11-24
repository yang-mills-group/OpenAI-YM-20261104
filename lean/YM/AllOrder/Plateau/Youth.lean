import YM.AllOrder.Plateau.Area
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau.Line
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration PhysicalNext Repeat Height Song Geo RG.Shoot
open Push.Uniform Blaze Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Shop Further.PhysicalPeriodLimitF933
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X : Metals G} {D:Rolls X.p} (A : Alloy X D) (F:Factor A) {c f : Side} {n m N k : ℕ}
open Ker Ker.Start Haiku Kinetic.Port Fire PertExtension.Series Radial Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open Sienna Coat Push.Uniform Brush BudgetPoint
variable {β:ℝ}
set_option quotPrecheck false
local notation "a" => A.B.a
local notation "J" => (A.B.a.clock.J (m+1))
local notation "I" => (A.B.a.clock.J m)
local notation "L" => (D.L J)
local notation "x₀" => (A.B.a.clock.hatBeta m)
local notation "z" => betaF G x₀ L
local notation "V" => A.B.a.budget m
local notation "P" => (F.target J I)
local notation "R" => F.shape
local notation "Ω" => (F.expense J I)
local notation "B" => radiusB x₀
local notation "γ" => (A.B.kin.alpha N m)
local notation "O" => Chi.canonical
local notation "hJ" => (A.B.a.clock.adm (m+1))
local notation "hp" => (A.B.a.clock.adm m)
local notation "K"=> X.p.kernel
local notation "Π"=> A.B.a.S.block m
local notation "s" => Mural.sheet X.p D hJ
local notation "W" => X.p.profile J
local notation "E" => X.p.profile I
local notation "u" => (tall I)
local notation "Y" => (parking u (P).halo)
local notation "d" => (Meadow.studio Y B)
local notation "R₁"=> A.B.kin.path N (m+1)
local notation "R₂"=> A.B.kin.path N m
local notation "Q₀"=> A.B.a.budget (m+1)
local notation "D₀"=>ConnectedActivityE6.loopBill G L x₀
local notation "H'"=> Shop.Pledged -- not yet
local notation "Γ"=> precinct D (i:=I) hJ
local notation "M"=> Bank D (i:=I) hJ
variable (π:f.val=c.val*(A.B.a.S.block m).val)(hβ:β∈band A.B.a (m+1))(hk:m<N)
local notation "S"=>Pane.panel A m π
local notation "T"=> orchestra A N π
variable {r:ℕ} (U:Bank (i:=A.B.a.clock.J m) D (A.B.a.clock.adm (m+1))) (hx: Plus D F.target (A.B.a.clock.adm (m+1)) U (A.B.a.clock.hatBeta m))
    (t:precinct D (i:=A.B.a.clock.J m) (A.B.a.clock.adm (m+1))) (h: Books A (m:=m) (N:=N) t) (hr:r ≤ A.B.a.clock.J m)
local notation "Z'"=> z^Shop.air I
local notation "M'"=> Plateau.shelter U.reps t (gStep β) B r c
local notation "Λ₀"=> (fun i:Γ=> i.paid)
local notation "b₀"=> (Plateau.Line.laurels D (i:=I) (j:=J) x₀)
lemma transparent {Q:BudgetPoint}{c:Side} (g:ℕ→RegularAddress c): Meadow.Budget Q g (fun _ (_:Config G c)=> (0:ℝ)) 0 := ⟨0,fun i=> by simp [SumBudget],fun i=>⟨CouplingShape.reg_const 0, CouplingShape.sup_larger (CouplingShape.sup_const 0) (le_of_eq abs_zero)⟩⟩ -- fun _ syntax
local notation "Φ"=> (Plateau.Line.breadth D F.target (i:=I) (j:=J) x₀)
local notation "τ"=> (Plateau.Line.sage D (i:=I) (j:=J) x₀)
local notation "O₀"=> (clock_pure A F (m:=m))
local notation "S₀"=> (size_pure A F (m:=m))
local notation "e₀"=> Trio.base Y B
-- model on ANY mesh. symmetry choir later22. note cabin master & clock
abbrev silk (β:ℝ)(k:ℕ)(i:Stars): Offer G (S₀ i):= shelter U.reps t (gStep β) B k (S₀ i)
local notation "ϕ"=> silk A F U t β r
abbrev beacon_star (β:ℝ)(r:ℕ): Offer G c:= Trio.ornament O₀ (silk A F U t β r)
local notation "F'"=> beacon_star A F U t (c:=c) β r
local notation "υ[n]"=> beacon_star A F U t (c:=n) β r
include hr
lemma beacon_full (W':Config G c): froth (F') W'=-Plateau.wealth U.reps t (gStep β) B r c W':= by
 unfold beacon_star; rw [fare_Lad O₀ (shelter U.reps t (gStep β) B r) ?_ ?_ W' (show 0<B from (V).B_pos) ?_]; -- need k= ?? B?
 · rw [stillA,froth_shelter,Pi.neg_apply,Pi.neg_apply,wealth_one Λ₀ U.reps U.canvas hr,neg_zero,sub_zero]
 · exact fun i=> shelter_turn U.reps t _
 · exact shelter_local U.reps t _
 unfold Trio.tent Meadow.studio; omega
variable (H:Lodge D F.shape (fun _ i=> edgeW i) A.delay) (Hf:Fair D F.target A.delay) (W':LineCare N m A F β)
include hx h hk hβ W'
lemma mantras (i:Stars) : Shop.Mantra A r (N:=N) (m:=m) (side_pure A F i) β (ϕ i):= Function.const _ (let he:100*(1+B)≤(S₀ i).val:= Trio.highChair Y B i|>.2
  have ht:Stores.till x₀ ≤ (S₀ i).val:= by unfold Stores.till; omega
  mapped A F (side_pure A F i) hβ U hx t h hr (Trio.taller ..) ht (W'.bought i|>.laws.data.room.larger)
  ) (hk)
include H Hf
local notation "U'"=>Boulevard.ticket (E).order b₀
local notation "X'"=>furl G L x₀
set_option maxHeartbeats 200000 in
lemma mantel (i:Stars)(x:Positions (Uniform.Primary (S₀ i) G))(he:flags (V).threshold (actual x)=∅)(ht:‖x‖+2*furl G L x₀ < Z') (l:List (Directions G (S₀ i))) (hf:l.length≤(V).order)(hq:∀ i∈l,‖i‖≤(V).threshold) :
   ‖leftDerivs (Boulevard.stillA (Trio.froth (ϕ i))) l (actual x)‖ ≤ U' := by
 let Z:= Y; let Y':= S₀ i; let Q:= W'.bought i; let Y₁:= (side_pure A F (m:=m) i); let K':= Classical.choice (Tree.select (Pane.panel A m Y₁).ratio (Pane.panel A m Y₁).patch.odd_side); obtain ⟨ρ,hρ,hK,hT⟩:= Shop.desk («K»:=K') A F H Y₁ Q hk rfl (Trio.taller ..)
 obtain ⟨hℓ,hφ,hV,-⟩:= Rain.jersey (A:=A) (m:=m); have hv : (V).threshold ≤2*Pressure.fiery G x₀ L:= by rw [← Q.laws.data.funds.length_eq]; exact Q.laws.data.room.temperatures
 let g := Trio.froth (ϕ i); let e x':= peal U.reps t (gStep β) B r Y' x'; let d': ℕ→ RegularAddress Y':=fun _=> leap 0 (0:Site Y'); let wt := laurels D (i:=I) (j:=J) x₀; let t':=Z'
 have hV (x':Config G (S₀ i)): g x'= -wealth U.reps t (gStep β) B r Y' x':= congr_fun (froth_shelter ..) x'
 have hp₀ : g 1=0:= by rw [hV,wealth_one Λ₀ U.reps U.canvas hr,neg_zero]
 have hX : Boulevard.stillA (-g) ∘ actual=e := by ext1 y; change -g _- -g _= _; rw [hp₀,hV]; change _=peal _ _ _ _ _ _ _; rw [wealth_eq,neg_neg,neg_zero,sub_zero]; -- defeq
 let g':= fun (_:ℕ)=> (0:Config G (S₀ i)→ℝ)
 have hB : (V).Regular univ g:= by rw [show g=∑ j,ϕ i j from funext fun i=> (Finset.sum_apply ..).symm]; exact Meadow.regularA _ fun s₁ _=> shelter_reg Λ₀ U.reps U.canvas hr (gStep β) t V _
 have hK := ((Hf _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)).2.2.2.2) (V) rfl hv hℓ (S₀ i) x ht he d' g' g (-g) wt 0 0 (transparent d') hB (fun j _=> (by simp [Boulevard.throng,g'])) (fun z₁ hκ heP=> ?_) l hf hq -- solve f v Bud
 · simpa only [mul_zero,add_zero] using hK
 have hu : Stores.till x₀ ≤ (Y').val:=by have hx:100*(1+B)≤Y'.val:= (Trio.highChair Y B i).2; unfold Stores.till; omega -- binder i shadow
 rw [hX]; have h'': 0<x₀:= Real.exp_pos 1|>.trans_le (((Shop.lot A F (m:=m) H).script 0 (Nat.zero_le _)).1)
 have hz:0 < X':=Real.rpow_pos_of_pos (by change 0<z; rw [← PriceCompiler.beta_eq A.B.valid]; exact zero_lt_one.trans (A.B.a.fits.delayed _)) _
 exact (Line.crossed A F Y₁ hβ U hx t h hr (Trio.taller ..) hu Q.laws.data.room.larger K' (Classical.arbitrary _) ρ hρ _ (lt_of_le_of_lt (le_add_of_nonneg_right (by positivity)) hκ)).2 -- shadow h
variable (hk0:2*(Trio.base (parking (tall (A.B.a.clock.J m)) (F.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo) (radiusB (A.B.a.clock.hatBeta m))) < c.val)
include hk0
lemma shell_pay : Meadow.Budget V (Marlin.leap (c:=c) e₀) F' τ := by
 have htβ:0 < z:= by rw [← PriceCompiler.beta_eq A.B.valid]; exact zero_lt_one.trans (A.B.a.fits.delayed _)
 let p':=V; let y:=Z'; let e:=e₀; let t':= U'
 let f:= F'; have hf i j : (V).Regular univ (ϕ i j):= shelter_reg Λ₀ U.reps U.canvas hr _ _ _ j -- ?
 obtain ⟨hℓ,hφ,hV,-⟩:= Rain.jersey (A:=A) (m:=m); have hg:t' ≥0:= by unfold t' Boulevard.ticket laurels; positivity
 have he : Trio.tent Y B+4≤e:= by unfold e Trio.base; omega
 let Q:= W'.bought 0; have hv : (V).threshold ≤2*Pressure.fiery G x₀ L:= by rw [← Q.laws.data.funds.length_eq]; exact Q.laws.data.room.temperatures
 have hz(i:Site c) : p'.Regular (neighbors e i) (f i)∧ p'.supBounds i (neighbors e i) (f i) Φ := by
    have hz j (k:Site (S₀ j)) : separation i (Slide.sites (pad O₀ j) i k)≤e:= (Slide.village (C:=S₀ j) (w:=Trio.tent Y B+j.val) (O₀ j).ge _ _).trans (by have hk:=j.isLt; omega)
    have hh j: p'.Regular univ (Boulevard.stillA (Trio.froth (ϕ j))):= by apply CouplingShape.reg_sub _ (CouplingShape.reg_const _); rw [show froth (ϕ j)=∑ i,ϕ j i from funext fun x=>(Finset.sum_apply ..).symm]; exact Meadow.regularA _ fun j _=>hf _ _
    constructor; · unfold f beacon_star; rw [orchard]; exact Meadow.regularA _ fun j _=> CouplingShape.reg_scale _ (Slide.regular (pad O₀ j) i (hh j) (fun k=> (neighbors_mem ..).2 (hz _ k)))
    have hP : Φ= oroW V e (fun _=> t') := by unfold oroW Trio.tilt; rw [hℓ,hφ]; rfl
    rw [hP]; apply Trio.kinds (V) O₀ e (ϕ) hf (fun _=>hg) he X' Z' i _ (Line.mantel A F hβ hk U hx t h hr H Hf W'); intro x ht u'; exact (Hf _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)).2.2.2.1 (V) hv _ _ hk0 _ (show Trio.tent Y B+u'.val+1 ≤ e from (by unfold e Trio.base; have hp' := u'.isLt; omega)) (O₀ u').ge i x ht
 refine ⟨fun _=> Φ,fun i=> ?_,fun i=> ⟨(hz i).1,(hz i).2⟩⟩; have hψ:0 ≤ Φ:= (hz 0).2.1
 apply budget_finite; · intro i; split; exact mul_nonneg hψ (Real.exp_pos _).le; rfl
 rw [Finset.sum_eq_single i]; rw [if_pos (show (leap e₀ i).site=i from rfl)]; rw [mul_comm]; refine le_trans (mul_le_mul_of_nonneg_right ?_ hψ) hx.2; apply Real.exp_monotone; have hh: preExponent V=Trio.stout E:=by unfold preExponent Trio.stout; rw [hV]
 rw [← hh]; apply mul_le_mul_of_nonneg_left _ (headline V|>.exponent_pos.le); unfold coverTicket; apply Nat.cast_le.mpr; apply (Trio.scaleMeters Y (radiusB x₀) (V).B_pos i e₀ (by omega)).trans; rw [two_mul]
 · intro j hj hh; exact if_neg hh
 simp
end YM.AllOrder.Plateau.Line
