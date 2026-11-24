import YM.MatchingLedger.Compass.Repeats

/-! # Uniqueness at *every* used step
 At fixed horizon & p, still compare by price on all replica periods. Can use divergent
 period and all precisions only in these exact plan equations; cannot infer quantitative
 regulator precision on a representative after C was chosen this way.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.MatchingLedger.Compass.Mirrors
open Function Filter Set MeasureTheory Precision RG Tree Wilson Lattice Work Exterior
open WilsonStartup.Change Extension.UV.LoopRate Extension.UV.StationaryData Bid
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {A:Levels G}{N m:ℕ}{U V:Crop A}{C:ChartRatio G} (ht:LocalRatio C)
local notation "D" p=>A.S.side m p
local notation "W"=> A.params (m+1)
variable (hA:Supply.AsDivisors A.S) (hx:m<N) (hU: U.Fires C) (hV: V.Fires C)
   (h : ∀ p, Stunning (A.params (m+1)).clip (A.S.side (m+1) p) (U.model N (m+1)) (V.model N (m+1)))
private abbrev token (V:Crop A) (p:ℕ)(m:ℕ) (N:ℕ) := H₂ (draft (c:=A.S.side m p) (V.alpha N m) (V.model N m) (A.params m).clip)

def size (A:Levels G) (m:ℕ)(p:ℕ): ℝ:= Fintype.card (Site (A.S.side m p))
lemma size_pos (A:Levels G) (m p:ℕ) : 0<size A m p:= Nat.cast_pos.mpr Fintype.card_pos
lemma size_grows (A:Levels G)(m:ℕ): Tendsto (fun j:ℕ=> ((A.S.side m j).val : ℝ)) atTop atTop := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp (tendsto_atTop_mono (f:=fun p=>(A.S.period p).val) (fun _=> Nat.le_mul_of_pos_right _ (A.S.denominator m).pos) A.S.period_strict.tendsto_atTop)

include hA hx ht hU hV h
lemma uniform_draft (p : ℕ) : token U p m N=token V p m N:=by
   obtain ⟨η,g,k,t,Hη,Hg,H⟩:= hU.each N m hx
   obtain ⟨η',g',k',t',Hη',Hg',H'⟩:= hV.each N m hx
   let θ(Z:Crop A)(p':ℕ) := draft (c:=D p') (Z.alpha N m) (Z.model N m) (A.params m).clip
   let e (j:ℕ):= (k*t)*Real.exp (-g*((D j).val:ℝ)) + (k'*t')*Real.exp (-g'*(D j).val)
   have hc(q:ℕ)(x y:Site (D q))(σ τ : TypeFace 1→G.ColorIndex→ℂ)(hv: ∀ i j, ‖σ i j‖≤1)(hP:∀ i j, ‖τ i j‖≤1): ContDiffAt ℝ ω (θ U q) 0 ∧ ContDiffAt ℝ ω (θ V q) 0 ∧
       |token U q m N ![wave x σ,wave y τ]-token V q m N ![wave x σ,wave y τ]| ≤ size A m q*e q:=by
       obtain ⟨F⟩:= Tree.select (A.clock.op m q).ratio (A.clock.op m q).patch.odd_side; let s:= Classical.arbitrary (A.clock.op m q).Choices
       obtain ⟨h₁,h₂,h₃,h₄⟩:= H q F; obtain ⟨-,h₅,-,h₆⟩:=H' q F
       let B:=![wave x (G:=G) σ,wave y τ]
       have he := equation F s ht h₂ h₅ (h q) (definite_of h₁ Hη s (h₂.2.2 s).1) ((h₄.branch s).self_of_nhds) -- agreement
       refine ⟨h₄.classicalResult,h₆.classicalResult,?_⟩
       have hu:= h₄.wave_price s x y σ τ hv hP; dsimp only at hu
       have ht:= h₆.wave_price s x y σ τ hv hP; dsimp only at ht
       let tκ:= thermal F s (W).clip (U.model N (m+1)) (U.station N m q F) C
       rw [← he.jets 2 le_rfl] at ht
       rw [abs_sub_comm] at hu
       refine le_trans (norm_sub_le_norm_sub_add_norm_sub (token U q m N B) (H₂ tκ B) (token V q m N B)) ?_; exact (add_le_add hu ht).trans_eq (by unfold e size;ring)
   apply takes; intro i j σ τ hs hl
   let z:Side:=D p; let x:= ![wave i (G:=G) σ,wave j τ]
   let v:=|token U p m N x-token V p m N x|
   choose f hf Hf using fun i:ℕ=> hA z i
   have hw:Tendsto f atTop atTop:= tendsto_atTop_mono (f:=id) (fun i=>hf i) tendsto_id
   have hz(q:ℕ): v≤ size A m p*e (f q):=by
      obtain ⟨L,hL⟩ := show z.val ∣ (D (f q)).val from dvd_mul_of_dvd_left (Hf q) _
      have hh:2≤z.val:= by have he:= A.fits.sizeT m p; change 100*(_+1) ≤ z.val at he; omega
      have he0:0<L:= Nat.pos_of_mul_pos_left (show 0< z.val*L from hL ▸ (D (f q)).pos)
      let c:= D (f q); let y:=wrap c (L • lift i); let a:=wrap c (L • lift j)
      obtain ⟨hx,hQ,hJ⟩:=hc (f q) y a σ τ hs hl
      have hZ(P:Crop A) (ht:ContDiffAt ℝ ω (θ P (f q)) 0) := gathers (P:=(A.clock.op m p).patch) (Y:= (A.S.oneStep m p).exact_size) (T:=(A.S.oneStep m (f q)).exact_size) hL hh (P.alpha N m) (A.params m).clip (P.model N m) ht i j σ τ
      change |H₂ (θ U (f q)) ![wave y σ,wave a τ]-H₂ (θ V (f q)) ![wave y σ,wave a τ]|≤ _ at hJ
      rw [show H₂ (θ U (f q)) ![wave y σ,wave a τ]=_ from (hZ U hx), show H₂ (θ V (f q)) ![wave y σ,wave a τ]=_ from (hZ V hQ),← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (↑(L^4):ℝ)),show size A m (f q)=(↑(L^4):ℝ)*size A m p from ?_,mul_assoc] at hJ
      · exact le_of_mul_le_mul_left hJ (by positivity)
      unfold size; rw [Lattice.site_card,Lattice.site_card,hL]; unfold z; push_cast; ring
   have heq (g:ℝ)(hg:0<g) : Tendsto (fun i:ℕ=> Real.exp (-g*((D i).val:ℝ))) atTop (𝓝 0):= Real.tendsto_exp_atBot.comp ((size_grows A m).const_mul_atTop_of_neg (neg_lt_zero.mpr hg))
   have hv:Tendsto e atTop (𝓝 0):=by simpa only [mul_zero,add_zero] using! (((heq g Hg).const_mul (k*t)).add ((heq g' Hg').const_mul (k'*t')))
   have hx:Tendsto (fun i:ℕ=>size A m p*e (f i)) atTop (𝓝 0):=by simpa only [mul_zero] using! ((hv.comp hw).const_mul (size A m p))
   exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (ge_of_tendsto hx (Eventually.of_forall hz)) (abs_nonneg _)))
end YM.MatchingLedger.Compass.Mirrors
