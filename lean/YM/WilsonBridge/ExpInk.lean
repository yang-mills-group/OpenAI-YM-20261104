import YM.WilsonBridge.Integrate
/-!
# Translating the Taylor conventions on the algebra (no field rank cap other than by grade)

The Haar piece is also an exact `exp0` at full field rank.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge
open MS MS.Book MS.Koszul MS.Swirl MS.Puff MS.Cylinder MS.Orbit
open MS.Book.Convolve Program Puff.Mom Puff.Engine Puff.SplitP Puff.Actors Puff.Dynamics Orbit.LogReal Orbit.Cog
open PertExtension GaussianScore Orb Function Finset Lattice MeasureTheory WilsonBridge.Polynomial
open Series Radial Series.Tested Cylinder.Taylor
open scoped BigOperators ContDiff Classical Topology Matrix
variable {V : Type} [Fintype V] {p : Sector V} {E F:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma ink_iter (f:E→ℝ)(h:germ f)(u:Unit→E)(n:ℕ): ink u f (List.replicate n ())=((iteratedFDeriv ℝ n f 0 (fun _=>u ()):ℝ):ℂ):= by
    induction n generalizing f with
    | zero=> simp
    | succ n ih=>
        rw [List.replicate_succ, ink, ih _ (germ_layer h _), iteratedFDeriv_succ_apply_right]
        exact congr_arg ((↑):ℝ→ℂ) ( DFunLike.congr_fun ((ContinuousLinearMap.apply ℝ ℝ (u ())).iteratedFDeriv_comp_left (i:=n) (h.fderiv_right (m:=ω) (by simp)) le_top) (fun _ => u ()) ) -- fin init
lemma local_jet (f:E→ℝ)(h:germ f)(u:Unit→E)(n:ℕ): (Actors.phase n) * ink u f (List.replicate n ()) = Radial.jet f n (u ()):= by rw [ink_iter f h]; simp [Actors.phase, jet]
local notation "M"=> PermV p
local notation "Θ"=> clock useN (Raw V ℂ)
local infixl:70 " ⋆ "=> product p
local infixl:70 " ★ "=> Actors.core (PermV p)
-- commuting even jets include pre-Wick normalizations. exponential before linking.
omit [Fintype V] in
lemma rank_zero_hat (F:Raw V ℂ): mask 0 F= coin (F []):= by rw [rank_zero_eq_coin (rankMod F 0), enough [] (F:=F) (h:=0) rfl]
omit [Fintype V] in
lemma clock_ranked (F:Raw V ℂ) : Θ (rankLevel 0 F)=rankLevel 0 (Tick (fun _=>1) F):= by
    funext n; have h:=tick_rank n (rankMod F n); change ((n:ℂ) • (mask (n+0:ℤ) F))=mask (n+0:ℤ) _ ; rw [add_zero,← h]; funext l; by_cases hh:(l.length:ℤ)=n; · change _* mask (n:ℤ) F l=_; rw [enough l hh, enough l hh]; rfl
    change _*mask (n:ℤ) F l=_; rw [strange l hh, strange l hh,mul_zero ]
variable {u:V→E} (hu:∀ i,p i=true → u i=0) {f:E→ℝ} (hf:germ f) -- remove bogus
local notation "R" => ink u f
local notation "W" => ink u (Real.exp ∘ f)
local notation "L" => rankLevel 0 R
local notation "S" => rankLevel 0 W
include hu hf
omit [Fintype V] in
lemma Dexp (x:V) : D x W= D x R ⋆ W := by
    have he : germ (Real.exp∘ f):= Real.contDiff_exp.contDiffAt.comp (0:E) hf
    rw [inktip, inktip, ← ink_mul _ hu (germ_layer hf _) he]
    apply inkit; filter_upwards [hf.eventually (by simp)] with t ht; unfold layer; rw [fderiv_comp t (Real.differentiableAt_exp) (ht.differentiableAt (by simp)),ContinuousLinearMap.comp_apply,(Real.hasDerivAt_exp _).hasFDerivAt.fderiv]; rfl
lemma ranked_exp (hz : f 0=0) : exp0 p L=S := by
    have he : germ (Real.exp∘ f):= Real.contDiff_exp.contDiffAt.comp (0:E) hf
    have hH : Happy useN L:= by change mask 0 _=0; rw [rank_zero_hat,drip,hz]; exact (funext fun l=>by cases l<;>rfl)
    have hv : L∈(M).guard:= FreeBV.even_level (ink_p _ hu f)
    have hm (K:Raw V ℂ) : From K 0:= fun l hl=> by omega
    apply tick_agree useN (actor p) (tick0 useN L)
    · rw [ show exp0 p L useN.origin= _ from Stencil.simple_E (actor p) L useN hH ]; change coin (1:ℂ)=mask 0 W; rw [rank_zero_hat,drip,Function.comp_apply,hz,Real.exp_zero,Complex.ofReal_one]
    · exact ( turn_clock useN (actor p) ).idea hv hH
    change Θ S=Θ L ★ S; rw [clock_ranked,clock_ranked]; have hS (F H:Raw V ℂ): rankLevel 0 F ★ rankLevel 0 H=rankLevel 0 (F ⋆ H):= funext fun i=> pairLevel i (hm F) (hm H); rw [hS, overture (fun _=>1) (F:=W) (ink_s _ hu he), overture (fun _=>1) (ink_s _ hu hf)]; simp_rw [one_smul,map_sum,LinearMap.sum_apply,times_assoc,Dexp hu hf] -- issue eta Tick1
end YM.WilsonBridge
