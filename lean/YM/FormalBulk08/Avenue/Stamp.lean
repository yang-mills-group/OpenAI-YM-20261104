import YM.FormalBulk08.Avenue.Belts
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
variable {x:Loc G 1}{η σ A B C:ℝ}{u r p:ℕ} {q:edgeL G→edgeL G→ℝ}
-- exact Kalm & cream for any test mark at leading
open City PowerSeries
section
variable {V U:Type} [Fintype V] (p:Pce V)(r:ℕ)
lemma hearth_prime (q:Matrix V V ℝ)(he:∀ i>r,marble i p=0): marble r (hearth q p)=marble r p:= (roaming q p r r he).trans (pageant_peak he)
end
open Tree
variable (o:Loc G 1)(P:Flight j u)(R:Lodge P.patch){K:KernelChoices}(h:P.patch.Branches K G)(W:Pot G)(ρ:ChartRatio G)(hW:Story W (pink K.penalty P.wing))(hP:4≤u)(hρ:LocalRatio ρ)(hL:2≤P.L.val)
variable {F Z: Anthem D G} {d:ℕ}
include h hW hP hρ
lemma wan (N:Side)(i)(hf:Wade o F r)(x:Site P.L)(p:Studio D):
   let y:=Kemp.banner r (stepsong P F hL p x) (N*P.patch.L)
   marble r (coeff 0 (tossed P ρ h R N i (stone W _) y))= pearl (trMean P R K N G) (sieve (N*P.patch.L) (carries (Lattice.lift x) (F (throughW x _ hL p) 0 r))):= by
    intro y; obtain ⟨v,B,hv,hB,H,-⟩:= colors G K.penalty K.penalty_pos P.legal
    let U:= stepsong P F hL p x; have he i: marble i (coeff 0 y)=sieve (N * P.patch.L) (U 0 i):= badge U (step_can o P _ hf hL p x) (step_agate o P _ hf hL p x) le_rfl _ _ _
    let M:=stone W (N*P.patch.L); have hx:= stoned_main hv.le hB.le (H P.wing).1 hW.toVivid hW.ink (N*P.patch.L); rw [flagPoint P R h N i M y ρ hρ hP hx, Lava.target, hearth_prime (coeff 0 y) r, he r]; rfl
    intro i hi; rw [he i, show U 0 i=0 from ?_,sieve_zero]
    by_contra hc; exact not_lt.mpr (step_can o P _ hf hL p x _ _ hc) hi
lemma war (N:Side)(i)(hf:Glyph o F l 0)(x:Site P.L)(p:Studio D):
    let y:= Kemp.banner l (stepsong P F hL p x) (N*P.patch.L)
    marble r (binned P.land K.penalty N (tossed P ρ h R N i (stone W _) y))= pearl (trMean P R K N G) (marble r (binned P.wing K.penalty (N*P.patch.L) y)):= by
    intro y; obtain ⟨v,B,hv,hB,H,-⟩:= colors G K.penalty K.penalty_pos P.legal
    unfold binned;rw [wink P R h N hP _ _ y _ hρ (stoned_main hv.le hB.le (H P.wing).1 hW.toVivid hW.ink _) (materia o (Lattice.lift x) (throughW x _ hL p) hf)]; exact Lava.target ..
lemma wins (hf:Glyph o F l 0)(hz:Wade o Z r)(he:∀ p,Z p 0 r=winner P.wing K.penalty l F p r)(x:Site P.L)(p:Studio D)(y:chain (edgeL G) r)(i:(n:Side)→(primary P.patch K n).Choices):
    Tendsto (fun n:Side=>
      let g (T:Anthem D G)(v):= Kemp.banner v (stepsong P T hL p x) (n*P.patch.L)
      marble r (binned P.land K.penalty n (tossed P ρ h R n (i n) (stone W _) (g F l))) (Lotus.drip n∘ y) - rancho (tossed P ρ h R n (i n) (stone W _) (g Z r)) 0 r (Lotus.drip n ∘ y)) atTop (𝓝 0):= by
    simp only [war o P R h W ρ hW hP hρ hL _ _ hf x p, rancho,wan o P R h W ρ hW hP hρ hL _ _ hz x p]
    obtain ⟨η,hη,H⟩:=kinkwind P.wing K.penalty K.penalty_pos P.legal (throughW x _ hL p) hf.summary (Lattice.lift x) r
    obtain ⟨σ,A,hσ,-,Q⟩:=step_bill o P Z hz hL 0 r
    let V:= Kemp.carries (Lattice.lift x) (Z (throughW x _ hL p) 0 r); have ht:Knoxville (fame _) σ (Lattice.lift x,o) V (A*‖p‖):= Q p x
    rw [←he] at H; obtain ⟨C,hC,X⟩:= fine_fee P R K G hP; exact still_raft H hη hσ (sieve_kalm V ht hσ.le) _ (onward P.patch.L) (fun n=> trMean P R K n G) X hC (fun n=> Lotus.drip n ∘ y)
lemma full_wrap (hf: Wade o F l)(p:Studio D)(d:ℕ)(i:(n:Side)→(primary P.patch K n).Choices):
   Light (winner P.land K.penalty l (quick P R W F ρ h hL d l) p r) (fun n=>marble r (binned P.land K.penalty n (quickP P R W F ρ h hL d l p n (i n)))):= by
    let X:= quick P R W F ρ h hL d l; let Y(n:Side):=quickP P R W F ρ h hL d l p n (i n)
    have hx: Wade o X l:= quick_Wade o P R _ W ρ h hf hW hρ hL hP le_rfl d
    have hy n: Young (rancho (Y n)) l:= quickP_breeze o P R W F ρ h hL hf hW hρ le_rfl hP p n _
    have hp (n:Side)(m:ℕ)(hv:l< m): marble m (coeff 0 (Y n))=0:= Classical.byContradiction (fun hu=> not_lt.mpr (hy n 0 m hu) hv)
    choose η hη ht hU using fun a:Fin (l+1)=> brig o P R F W ρ h hf hW hρ hL hP le_rfl i 0 a.val d
    obtain ⟨v,u,V⟩:= Finset.exists_min_image Finset.univ η Finset.univ_nonempty
    have hh m : Kalm (η v) (0,o) (X p 0 m) (fun n=>marble m (PowerSeries.coeff 0 (Y n))):= by
       by_cases h':l< m
       · rw [show X p 0 m=0 from Classical.byContradiction (fun he=>not_lt.mpr (hx.1 p 0 m he) h')];simp_rw [hp _ _ h']; exact ⟨fun v=>tendsto_const_nhds,0,.of_forall fun n=>Knox_zeros _⟩
       let a:Fin (l+1):=⟨m,by omega⟩; obtain ⟨P,C,H⟩:= ht a p; exact ⟨P,C,H.mono fun _ he=>penn_shrink he (V a (Finset.mem_univ _))⟩
    exact (kain P.land K.penalty_pos hP _ Y hh hp (hη v) _).1
lemma angels (hf:Glyph o F l 0)(hz:Wade o Z r)(he:∀ p,Z p 0 r=winner P.wing K.penalty l F p r)(p:Studio D)(d:ℕ):
    winner P.land K.penalty l (quick P R W F ρ h hL d l) p r=quick P R W Z ρ h hL d r p 0 r:= by
   let i n:= Classical.choice (chooseable n _ (primary P.patch K n)); funext v; have hV:=full_wrap o P R h W ρ hW hP hρ hL hf.summary p d i (r:=r) v
   obtain ⟨η,hη,Q,-⟩:= brig o P R Z W ρ h hz hW hρ hL hP le_rfl i 0 r d
   apply sub_eq_zero.mp (tendsto_nhds_unique (hV.sub ((Q p).1 v)) (?_));
   let X n x:= (marble r (binned P.land K.penalty n (tossed P ρ h R n (i n) (stone W _) (Kemp.banner l (stepsong P F hL p x) (n*P.patch.L)))))
   have heq n: marble r (binned P.land K.penalty n (quickP P R W F ρ h hL d l p n (i n)))= aven P.L d •∑ x:Site P.L,X n x:= by simp only [quickP,binned,coeff_C_mul,map_sum,←MvPolynomial.smul_eq_C_mul,map_smul,←canyon_eq]; rfl --
   have hX:= tendsto_finsetSum (Finset.univ: Finset (Site P.L)) (fun x _=> wins o P R h W ρ hW hP hρ hL hf hz he x p v i); have hU:= hX.const_mul (aven P.L d); simp only [Finset.sum_const_zero,mul_zero] at hU; apply hU.congr'; filter_upwards with n; rw [heq,quick_income,Finset.sum_sub_distrib,mul_sub]; simp only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul];rfl
end YM.FormalBulk08.Avenue
