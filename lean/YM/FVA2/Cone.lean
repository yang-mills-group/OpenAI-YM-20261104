import YM.FVA2.RadialMatch
import YM.FVA2.TreeWick
import YM.PertExtension.OrbParity

/-!
# The concrete tree prescription is `Orb.diag`

No perturbative truncation/re-estimation error is taken before normalizing.
The matrix of all Gaussian integrals here is not asserted uniformly bounded
as the finite volume tends to infinity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion.Cone
open Finset Function Filter MeasureTheory Lattice Precision
open MS MS.Koszul MS.Book MS.Book.Convolve MS.Cylinder MS.Cylinder.Taylor MS.Bare
open MS.Native MS.Swirl MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal
open MS.Puff MS.Puff.Actors MS.Puff.Engine MS.Puff.Mom MS.Puff.Dynamics
open PertExtension PertExtension.Orb PertExtension.GaussianScore PertExtension.Series
  PertExtension.Series.Radial
open ArrayMap Ends Choice Bosonic
open scoped Topology ContDiff Classical
variable {G : Gauge} {n : Side} (h : Even n.val)
local notation "T₀"=> canonical G h
local notation "I" => Z G (Cotree n)
local notation "L"=> baseChart G (Cotree n)
local notation "γ"=> tangentVec
local notation "H"=> Ends.measure_term (A:=Cotree n) (G:=G)
local notation "σ"=> plain (Z G (Cotree n))

abbrev Csort (r:ℕ) : Raw (Z G (Cotree n)) ℂ :=
  if r=0 then 0 else -Book.mask (r+2:ℤ) (ink L fiscal)
lemma unitH : H 0=0:=by simp [measure_term,Maurer.lac,LocalH.spin_zero G]
lemma rooted_order (x : Dir G n) :
    Ends.exp_A ((T₀).send_A x) = splitLink (1:Trees n→G.El) (fun i:Cotree n=>G.lieExp (x i)) := by
  funext i
  change G.lieExp ((extend_zero (fun i:OEdge n=>¬Branch i) G x) i)= _
  by_cases ht:Branch i <;> simp [extend_zero,splitLink,ht]
lemma side_H (x : Dir G n) : Ends.measure_term ((T₀).send_A x)=Ends.measure_term x := by
  change Ends.measure_term _= ∑ i:Cotree n,_
  unfold Ends.measure_term; -- sum subtype
  let f (i:OEdge n):=Maurer.lac ((T₀).send_A x i)
  change ∑ i:OEdge n,f i=_
  trans ∑ i∈ (Finset.univ.filter fun i:OEdge n=>¬Branch i), f i
  · symm; refine Finset.sum_subset (Finset.subset_univ _) (fun i _ hi=> ?_)
    simp at hi
    change Maurer.lac ((extend_zero (fun i:OEdge n=>¬Branch i) G x) i)=0
    simp [extend_zero,hi,Maurer.lac,LocalH.spin_zero G]
  rw [Finset.sum_subtype _ (p:=(fun i:OEdge n=>¬Branch i)) (by simp)]
  refine Finset.sum_congr rfl (fun i hi=>?_); rcases i with ⟨i,hb⟩
  unfold f; change Maurer.lac ((extend_zero (fun i:OEdge n=>¬Branch i) G x) i)=_
  simp [extend_zero,hb]
lemma basis_send (G:Gauge)(n:Side) : (Native.priv (G:=G) (Q:=Cotree n))=⇑(baseChart G (Cotree n)):= funext (fun i=>(base_at i).symm)
lemma onSlice : (T₀).boson = Csort (G:=G) (n:=n) + rankLevel 0 (ink L H) := by
  funext r; rw [boson]; unfold Csort; split_ifs with hr; · subst r; rw [ Pi.add_apply, if_pos rfl,zero_add, rank_zero L _ unitH ]; rfl
  rw [Pi.add_apply, Pi.add_apply, Choice.co_slice _ _ (prior_root_prop ..).smooth, Choice.co_slice _ _ (Ends.measure_germ), if_neg hr]
  change rankLevel 2 (ink (Native.priv (Q:= Cotree n)) (priorRoot G n ∘ (show Orb.Dir G n → RootX G n from (T₀).send_A))) r+
    rankLevel 0 (ink (Native.priv (Q:=Cotree n)) (Ends.measure_term ∘ (show Orb.Dir G n → RootX G n from (T₀).send_A))) r=
    -mask (r+2:ℤ) (ink L fiscal)+rankLevel 0 (ink L H) r
  rw [    basis_send,show priorRoot G n ∘ _ = -fiscal from ?_, show Ends.measure_term ∘ _= H from funext (fun y=>side_H h y)]
  · rw [← neg_one_smul ℝ (fiscal),ink_smul L fiscal_smooth.contDiffAt]; unfold rankLevel; rw [map_smul]; simp
  funext x; change -(Wilson.energy (liftLinks (Ends.exp_A ((T₀).send_A x)))/2)=-fiscal x; rw [rooted_order]; rfl
lemma visible_W : (T₀).relative = (PermV σ).core (exp0 σ Csort) (rankLevel 0 (ink L (Real.exp∘ H))) := by
  have he : (T₀).relative = exp0 σ (Csort + rankLevel 0 (ink L H)):= by
    refine congr_arg (exp0 σ) ?_ ; exact onSlice h
  rw [he]; unfold exp0; rw [cheer_a (guarded _) (guarded _) (show Actors.Happy useN (Csort (G:=G) (n:=n)) from if_pos rfl) (rank_zero L _ unitH), ← eta_exp L _ unitH measure_germ]
lemma prior_coordinates (O:Orb.Observable G n) :
    (accountingWith (tray G) O) =ᶠ[𝓝 0]
      (tray G).scale ^ (Fintype.card (Cotree n)) • ((Real.exp ∘ H)*(O ∘ PertExtension.Chart.expLinks G _)) := by
  obtain he:= Maurer.real_ratio (traySpec G)
  filter_upwards [eventually_all.mpr (fun i:Cotree n=> (continuous_apply i|>.tendsto (0:Dir G n)).eventually
    (he.and (Maurer.lives G)))] with x hx
  have hJ : (PertExtension.Chart.jacobian (tray G)) x=
      (tray G).scale ^ (Fintype.card (Cotree n))* Real.exp (H x) := by
    unfold measure_term; rw [Real.exp_sum, show (tray G).scale ^ _ = ∏ _i:Cotree n,(tray G).scale by simp, ← Finset.prod_mul_distrib];
    refine Finset.prod_congr rfl (fun i hi=>?_); rw [PertExtension.Chart.fee,(hx i).1,Maurer.lac,Real.exp_log (hx i).2]
    exact max_eq_left (mul_nonneg (traySpec G).scale.le (hx i).2.le)
  rw [accountingWith,hJ,mul_assoc]; rfl
lemma thinL (i j: I) : Chill ((T₀).lineCo : Matrix I I ℂ) i j=
     ((Orb.saddle h (G:=G)).wick (Module.Basis.coord L i) (Module.Basis.coord L j):ℂ) := by
  unfold Choice.lineCo; rw [(canonical_inv (G:=G) h)]
  have ht:= (Orb.saddle h (G:=G)).turns ((Orb.saddle h).inverse (Module.Basis.coord L j)) ((Orb.saddle h).inverse (Module.Basis.coord L i));
  rw [ (Orb.saddle h).applies,(Orb.saddle h).applies ] at ht
  change 2*((2:ℂ)⁻¹ * ↑((Module.Basis.coord L i) _))=_
  rw [← mul_assoc,mul_inv_cancel₀ (by norm_num),one_mul,← ht]; rfl

include h
lemma Γ_rankE (i : ℕ) (F:Dir G n→ℝ)(hk:germ F) : Γ (rankLevel (i:ℤ) (ink L F)) σ := by
  intro j _
  refine ⟨ ?_,minH (Limit.mod _ _)⟩
  exact Choice.boson_regular.symRank T₀ _ (ink_s _ (fun _ h=> Bool.noConfusion h) hk)
lemma Csort_Γ : Γ (Csort (G:=G) (n:=n)) σ:= by
  intro i _; unfold Csort; split; exact (FeeP σ).zero_mem
  exact (FeeP _).neg_mem ((Γ_rankE h 2 _ fiscal_smooth.contDiffAt) i (Set.mem_univ _))

local notation "M" => PermV σ
set_option quotPrecheck false
local notation "c" => (tray G).scale ^ (Fintype.card (Cotree n))
local notation "eO"=> PertExtension.Chart.expLinks G (Cotree n)
local notation "ι"=> PertExtension.Chart.tangent G (Cotree n)

abbrev EMark (O:Orb.Observable G n) := rankLevel 0 (ink (baseChart G (Cotree n)) (O ∘ eO))
def insertion_body (O:Orb.Observable G n) := (PermV σ).core (show SpecB (Z G (Cotree n)) from (T₀).relative) (EMark O)

variable {O:Orb.Observable G n} (hO : germ (O ∘ PertExtension.Chart.expLinks G (Cotree n)))

lemma floor_x (x:Dir G n)(k:ℕ) : Bosonic.value (Module.Basis.coord L) (exp0 σ Csort k) x =
    (expsum (Radial.layers fiscal) k k x:ℂ) := by
  rw [Bosonic.value,← promised (Bosonic.eval (fun i=> (↑(Module.Basis.coord L i x):ℂ))) (exp0 σ Csort), eval_exp _ _ (Csort_Γ h)]
  let V(a:I):= (↑(Module.Basis.coord L a x):ℂ)
  let A:=promote (Bosonic.eval V) (Csort (G:=G) (n:=n))
  have he i : A i= ↑(Radial.layers fiscal i x) := by
    change Bosonic.eval V (Csort i)=_; unfold Csort Radial.layers; by_cases hi:i=0; swap
    · rw [if_neg hi,if_neg hi,add_zero,map_neg,← show (↑(i+2:ℕ):ℤ) = _ from (by push_cast; rfl : (↑(i+2:ℕ):ℤ)= (i:ℤ)+2) ]
      rw [Complex.ofReal_neg]; exact congr_arg Neg.neg (value_jet L fiscal fiscal_smooth.contDiffAt (i+2) x)
    rw [hi, if_pos rfl, if_pos rfl,map_zero, neg_add_cancel]; rfl
  have hp i j: Trunk.power A i j=Complex.ofReal (Zone.TaylorPow (Radial.layers fiscal) i j x):= by
    induction i generalizing j with
    | zero=> by_cases h:j=0
             · subst j; change (useN.refineV _) _=Complex.ofReal (Zone.TaylorPow (Radial.layers fiscal) 0 _ x); rw [SplitP.refineV,if_pos (show 0=useN.origin from rfl)]; simp [Toy,Zone.TaylorPow]
             change (useN.refineV _) _=Complex.ofReal (Zone.TaylorPow (Radial.layers fiscal) 0 _ x); rw [SplitP.refineV,if_neg (show j≠useN.origin from h)]; simp [Zone.TaylorPow,h]
    | succ i IH=>
      change (∑ d∈antidiagonal j, A _ * Trunk.power A i d.2 )=_
      simp only [Zone.TaylorPow,Zone.mul,Complex.ofReal_sum,Complex.ofReal_mul, IH,he]
      -- maybe antidiagonal swap order
      conv_lhs => rhs; ext z; rw [mul_comm] -- syntax lhs rw alt
      exact Finset.Nat.sum_antidiagonal_swap (f:=fun w=> Complex.ofReal (Zone.TaylorPow (Radial.layers fiscal) i w.1 x) * Complex.ofReal (Radial.layers fiscal w.2 x))
  change (∑ i∈Finset.range (k+1),Actors.phase i • Trunk.power A i) k= _
  rw [Finset.sum_apply,expsum, Complex.ofReal_sum]; refine Finset.sum_congr rfl fun i _=>?_; rw [Pi.smul_apply,smul_eq_mul, hp]; push_cast; rfl

include hO
lemma vacuum_merge (k:ℕ)(x:Dir G n): ↑(integrandSeries fiscal (accountingWith (tray G) O) k x)=
    Complex.ofReal (c)*value (Module.Basis.coord L) (insertion_body h O k) x := by
  let G':=O ∘ eO; let W : Dir G n→ℝ:= Real.exp ∘ H
  let Z:= accountingWith (tray G) O
  have hx : germ W:= Real.contDiff_exp.contDiffAt.comp 0 measure_germ
  have hF : germ (W*G'):= hx.mul hO
  have hg : germ Z:= (show germ (c • (W*G')) from hF.const_smul c).congr_of_eventuallyEq (prior_coordinates O)
  have ht : Complex.ofReal (c) • ((M).core (rankLevel 0 (ink L W)) (EMark O))= rankLevel 0 (ink L Z) := by
    funext i; change Complex.ofReal (c) • (pairW (product σ) (rankLevel 0 (ink L W)) (EMark O) i)=_
    conv_rhs => rw [rankLevel,show ink L Z=_ from inkit L (prior_coordinates O), ink_smul L hF, ink_mul L (p:=σ) (fun _ h=> Bool.noConfusion h) hx hO, map_smul]
    exact congr_arg (fun v'=> Complex.ofReal (c) • v') (pairLevel i (p:=σ) (show Book.From (ink L W) 0 from fun l hl=>by omega) (show Book.From (ink L G') 0 from fun l hl=>by omega))
  have heZ : Γ (rankLevel 0 (ink L Z)) σ:= Γ_rankE h 0 Z hg
  let τ:= exp0 σ Csort
  have he : Complex.ofReal (c) • insertion_body h O= (M).core (rankLevel 0 (ink L Z)) τ := by
    rw [insertion_body, visible_W, (M).star_a,← map_smul,show Complex.ofReal (c) • _=rankLevel 0 (ink L Z) from ht, Inserted.even_central (guarded τ) ] -- typeclass defeq
  have Ht:= eval_multiply (fun i:I=> (↑(Module.Basis.coord L i x):ℂ)) _ τ heZ (expΓ (Csort_Γ h))
  rw [show Complex.ofReal (c)*value (Module.Basis.coord L) (insertion_body h O k) x= Bosonic.value (Module.Basis.coord L) ((Complex.ofReal (c) • insertion_body h O) k) x from ?_,he]; swap; · unfold value; simp
  unfold integrandSeries Zone.mul; rw [Complex.ofReal_sum, show value (Module.Basis.coord L) ((M).core _ τ k) x = _ from congr_fun Ht k];
  apply Finset.sum_congr rfl; intro i _; rw [Complex.ofReal_mul]; change _ = value (Module.Basis.coord L) (rankLevel 0 (ink L Z) i.1) x * value (Module.Basis.coord L) (τ i.2) x; rw [show value (Module.Basis.coord L) _ x= _ from floor_x h x i.2]; unfold rankLevel; rw [add_zero, value_jet L Z hg]

/-- Factor removed together with Gaussian at tree-sliced origin. -/
abbrev baseNum (G:Gauge)(n:Side):ℂ:= Complex.ofReal ((tray G).scale ^ Fintype.card (Cotree n) * ∫ x : Dir G n,kernel fiscal x ∂(PertExtension.Chart.tangent G _))
local notation "C"=>baseNum G n

omit hO in
lemma primary : C≠0 := by
  have hH : 0<c:=pow_pos (traySpec G).scale _
  have hV:= integral_exp_pos (ker_integrable h (G:=G)); exact Complex.ofReal_injective.ne ((mul_pos hH hV).ne')

lemma revenues (k:ℕ) : Complex.ofReal (Orb.rows O k) = C*View ((T₀).lineCo : Matrix I I ℂ) (insertion_body h O k) := by
  let Λ:=(Orb.saddle h (G:=G))
  let F:=insertion_body h O
  have hs : Γ F σ:=ΤΓ_pair ((show Γ (T₀).relative σ from expΓ ((T₀).boson_regular))) (Γ_rankE h 0 (O∘ eO) hO)
  have hx:= wick_eval Λ (Module.Basis.coord L) _ (thinL h) ι (F k) (fee_spec (hs k (Set.mem_univ _))).1 (fee_spec (hs k (Set.mem_univ _))).2
  unfold Orb.rows Orb.rowsWith Radial.moment baseNum normTerm
  conv_lhs => rw [← integral_complex_ofReal]; simp only [Complex.ofReal_mul,vacuum_merge h hO k]
  rw [show ∫ x:Dir G n,_ ∂ι = Complex.ofReal (c) *
        ∫ x:Dir G n,(Λ.kern x : ℂ)*value (Module.Basis.coord L) (F k) x ∂ι from ?_, hx.equal, Complex.ofReal_mul,saddleLaw h,mul_assoc]; rfl
  rw [← integral_const_mul]; refine integral_congr_ae (Eventually.of_forall (fun x=> ?_)); rw [saddleLaw h]; unfold Λ F; ring

omit hO in
lemma empty_cost (k:ℕ) : Complex.ofReal (Orb.rows (G:=G) (n:=n) 1 k)= C* ℶV ((T₀).lineCo : Matrix I I ℂ) ((T₀).relative) k := by
   rw [revenues (O:= (1:Orb.Observable G n)) h contDiffAt_const, insertion_body,
     show EMark (1:Orb.Observable G n)=(M).unit from ?_, (M).identityR];
   · rfl
   have Hc : (1:Orb.Observable G n) ∘ eO=(fun _=>1) := rfl
   unfold EMark; rw [Hc,ink_const]; funext i; unfold rankLevel; by_cases he:i=0
   · subst i; rw [show (M).unit 0=coin 1 from if_pos rfl]; ext l; rcases l with _|l <;> simp [Book.mask,coin]
   rw [show (M).unit i=0 from if_neg he]; ext l; rcases l with _|l
   · simp only [Book.mask]; exact if_neg (by simp; omega)
   simp [Book.mask,coin]

lemma canonical_diagram : Endμ ((T₀).lineCo : Matrix I I ℂ) σ (show SpecB I from (T₀).boson) (EMark O)
    (fun k=> Complex.ofReal (Orb.diag O k)) := by
   funext k
   apply mul_left_cancel₀ (primary (G:=G) h)
   change C*View ((T₀).lineCo : Matrix I I ℂ) (insertion_body h O k) = C*(_)
   rw [← revenues h hO]
   have hr := congr_fun (Orb.rows_with_head (traySpec G) h O) k
   change Tested.conv (Orb.diag O) (Orb.rows (n:=n) (1: Orb.Observable G n)) k=Orb.rows O k at hr
   rw [← hr, Tested.conv,Tested.term,PowerSeries.coeff_mul]
   conv_lhs => simp only [PowerSeries.coeff_mk,Complex.ofReal_sum,Complex.ofReal_mul]
   change ∑ i∈antidiagonal k,_= C * (∑ j ∈ antidiagonal k, ℶV ((T₀).lineCo : Matrix I I ℂ) ((T₀).relative) j.1 * Complex.ofReal (Orb.diag O j.2))
   rw [Finset.mul_sum]
   simp_rw [empty_cost h]
   rw [show (∑ i∈antidiagonal k,_)=_ from useN.also (fun i j=>Complex.ofReal (Orb.diag O i)*(C* ℶV ((T₀).lineCo : Matrix I I ℂ) ((T₀).relative) j)) k];
   exact Finset.sum_congr rfl (fun i _=> by ring)

omit hO

/-- The concrete choice in `Orb.diag` agrees with the rooted master convention
used in the finite bridge. No normalization by unrelated vacuum.
Only asserting this analytic cylinder version (or the corresponding formal extensions). -/
theorem WickOnRoot {O: Wilson.Config G n →ℝ}
    (F:RootX G n→ℝ) (hF:F=O ∘ Orb.liftLinks ∘ Ends.exp_A) (hg:germ F)
    (hI: Focus.Inert (root n).locus F)
    (V:Matrix (Z G (OEdge n)) (Z G (OEdge n)) ℂ)(B:Matrix (Ends.Z G (Vert n)) (Z G (OEdge n)) ℂ)
    (hv:V.transpose=V)(hh:B*Substitute.intoC (gaugeMatrix G n)=1)
    (hk:V*Substitute.intoC (hesT G n)=1-Substitute.intoC (gaugeMatrix G n)*B) :
    Endμ (Letter.grain V B) Letter.p (rootedVertex G n) (rankLevel 0 (ink tangentVec F)) (fun k=>Complex.ofReal (Orb.diag (Orb.restrictedO O) k)) := by
  let T:= canonical G h; let Z:= root n; let W:= Orb.restrictedO O
  have he: F ∘ (T.send_A)= (W∘ PertExtension.Chart.expLinks G (Cotree n)) := by
    rw [hF]; funext x; dsimp only [Function.comp_apply]; unfold T; rw [rooted_order]; rfl
  have hhF : germ (F ∘ T.send_A):= (show ContDiffAt ℝ ω F (T.send_A 0) from by rw [map_zero]; exact hg).comp 0 T.send_A.contDiff.contDiffAt
  have hW : germ (W ∘ eO):= he ▸ hhF
  have hb:= mark_insert Z (prior_root_prop G n) F 0 hg (fun l hl=>by omega) hI
  have hp := T.compares_root h _ hb _ (T.comark_regular 0 F hg) (T.all_monomial F hg 0) V B hv hh hk (fun k=> Complex.ofReal (Orb.diag W k))
  refine hp.mpr ?_
  have hE : T.comark F 0= EMark W:= by
    rw [comark,Choice.co_slice _ _ hg]
    have ht:=basis_send G n
    change rankLevel 0 (ink (Native.priv (G:=G) (Q:=Cotree n)) (F∘ T.send_A))=EMark W
    rw [ht]; exact congr_arg (fun z: Dir G n→ℝ=> rankLevel 0 (ink (⇑L) z)) he
  rw [hE]
  exact canonical_diagram h hW
end YM.FVA2.Inversion.Cone
