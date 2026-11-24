import YM.FVAAlt2.Convert.Cane
/-! Reweighting within finite-dimensional position frame.S closure. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Mass
open Function Finset Filter MeasureTheory Topology Set Metric
open Labels Precision Extra.FD Maxwell Extraction FormalOPE FormalOPE.RG10 RG10.Position.Grade
open PertExtension PertExtension.LatticePT PertExtension.Position PertExtension.Position.Triangle RG10.Position RG10.Gazebo RG10.Carryon RG10.InversionTop
open MS MS.Koszul MS.Menus MS.Book MS.Local.Physical MS.Land
open PowerSeries (C coeff constantCoeff)
open Home Home.Report Matrix Home.Profiles Convert Next.UVStress
open scoped Topology BigOperators PowerSeries ContDiff Classical Matrix
variable {G:Gauge}{F:Frames G}{d k n:ℕ}
local notation "V" d=> RG10.Position.Deck F d
local notation "FW"=>Matrix ( V d ) ( V d ) fps
local notation "LQ"=>Matrix (V d) ( V d ) ℝ
local notation "Ω"=> constantCoeff (R:=ℝ)
local notation "θ"=> Deck.price F d
variable {A B: Matrix ( RG10.Position.Deck F d ) ( RG10.Position.Deck F d ) fps}
structure Weight (A:Matrix ( V d ) ( V d ) fps) : Prop where
 zeroA: Stg A 0=1
 axis: Upright A
namespace Weight
lemma at_zeroW (h:Weight A): A.map Ω=1:= by rw [ ← h.zeroA ]; ext i j; simp [Stg]
lemma det (h:Weight A): IsUnit A.det:=by rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det ]; change IsUnit (A.map Ω).det; rw [at_zeroW h]; simp
lemma mult (h:Weight A)(hx:Weight B):Weight (A*B):=by
 refine ⟨?_,h.axis.mul hx.axis⟩; have he:(A*B).map Ω=1:= by rw [Matrix.map_mul,h.at_zeroW,hx.at_zeroW,mul_one]
 rw [← he]; ext i j; simp [Stg]
lemma later (h:Weight A)(hn:0<n): stamp A n∈ tents F d:= (h.axis).higher n hn -- order check
lemma held (h:Weight A)(n:ℕ): Cut θ (stamp A n):= by
 rcases Nat.eq_zero_or_pos n with hx|hx; · subst n; change Cut θ (Stg A 0); rw [ h.zeroA ]; apply layer_cut (tiled_one θ)
 exact (votes _|>.1 ( ( pinned _ ).mp (h.later hx)|>.1 )).1
lemma off_bill (h:Weight A): Cut θ A:= by intro i j he; ext1 k; exact (h.held k i j he).trans (map_zero (coeff k)).symm
-- Tigor (conjugating under tilted rotations)
private lemma liftTile {U:LQ}(h:U ∈ tents F d): tile θ U∈ tents F d:= by
 obtain ⟨h,hu⟩:= (pinned _).1 h; obtain ⟨hC,hH⟩:= ( votes _ ).1 h; refine (pinned _).2 ⟨ ( votes _ ).mpr ⟨ layer_cut ( tile_layer ),fun s=>?_⟩, ?a⟩; swap; · funext i; unfold Position.Grade.tile; rw [of_apply]; split; exacts [congr_fun hu i,rfl]
--_fun hu i
 have hs : Layer ( Deck.price F d ) ( swing d s ):= swing_grade d s; let B:= swing ( F:=F ) d s; have hB : Cut θ B:= layer_cut hs
 change tile θ U * B=B * tile θ U; have H : B * U=U*B:= Eq.symm (hH s); have he:tile θ B=B:= layer_fixed hs; change Cut θ U at hC; have ht:= hC.tile hB; -- root
 change tile θ ( U * B )= tile θ U * tile θ B at ht; rw [ he ] at ht; rw [← ht,← H,Cut.tile hB hC,he] -- pattern hC.of vs U
lemma tiled (h:Weight A): Weight (tile θ A):= by
 have ht:∀ i, Stg ( tile θ A ) i= tile θ ( Stg A i ):=fun i=> (by change stamp _ _=tile _ (stamp A i); rw [ canvas_tile ])
 have he: Stg ( tile θ A ) 0=1:= by rw [ht,h.zeroA, layer_fixed (tiled_one _)]
 refine ⟨he, Upright.obtainable _ ?_ (fun i hi=>?_)⟩; · rw [he,sub_self]; exact Submodule.zero_mem _
 rw [ht]; exact liftTile (h.later hi)
-- inverse of weight. Via stamps and oriented tangent multiplication
private lemma times {A B:LQ}(h : A∈tents F d) (k:B∈tents F d) : A*B ∈ tents F d:= by
 obtain ⟨ha,hx⟩:= (pinned (F:=F) _).1 h; obtain ⟨hb,_⟩:= (pinned (F:=F) _).1 k
 have hs:= (votes _).1 ha; have ht:= (votes _).1 hb; refine ⟨(votes _).mpr ⟨(Cut.mul hs.1 ht.1),?_⟩,funext fun i=>?_⟩
 · intro s
   let S:=swing (F:=F) d s; change (A*B)*S=S*(A*B); have ha : A*S=S*A:= hs.2 s; have hb:B*S=S*B:= ht.2 s; rw [mul_assoc,hb,← mul_assoc,ha,mul_assoc]
 change (A*B) (Deck.start F d) i=0; rw [Matrix.mul_apply]; refine sum_eq_zero fun j _=>mul_eq_zero_of_left (congr_fun hx j) _
lemma invert (h:Weight A): Weight A⁻¹:=by
 let B:=A⁻¹; have he:A*B=1:= Matrix.mul_nonsing_inv A h.det
 have hd: stamp A 0=1:= h.zeroA;
 have hu(n:ℕ): ∑ i ∈ Finset.HasAntidiagonal.antidiagonal n, stamp A i.1 * stamp B i.2=stamp (1:FW) n:=by rw [← Retry.stamped,he]; -- notation `hu` shadow
 have hv: stamp B 0=1:=by obtain H:= hu 0; simp only [Finset.Nat.antidiagonal_zero,sum_singleton,hd,one_mul] at H; exact H.trans ( RG10.Carryon.diag_at.trans RG10.Carryon.diag_one.symm ) -- via Stg
 refine ⟨hv, Upright.obtainable _ (by change stamp B 0-1∈ tents F d; rw [hv,sub_self]; exact Submodule.zero_mem _) ?_⟩; intro i
 induction i using Nat.strong_induction_on with
 | h i ih=>
   intro hi; let S:= Finset.HasAntidiagonal.antidiagonal i; change stamp B i∈ tents F d; obtain H:= hu i
   let f:=fun i:ℕ×ℕ=> stamp A i.1*stamp B i.2; rw [ ← Finset.add_sum_erase S f (by simp [S] : ((0,i):ℕ×ℕ)∈ S) ] at H -- f pattern?
   rw [ show stamp B i= -(∑ k∈S.erase (0,i),f k) from ( eq_neg_of_add_eq_zero_left ( (show stamp B i+_=stamp (1:FW) i from (by rw [show f (0,i)=stamp B i from Eq.trans (congr_arg ( · * stamp B i ) hd) (one_mul _)] at H; exact H) ).trans ( RG10.Carryon.zero_at i hi ))) ]; apply Submodule.neg_mem; apply Submodule.sum_mem; intro k hk; unfold f; obtain ⟨hk,hj⟩:=mem_erase.mp hk; have hq:k.fst+k.snd=i:= by simpa only [S,Finset.HasAntidiagonal.mem_antidiagonal] using hj
   have hh:0<k.fst:=by grind; -- proof
   by_cases hx:0<k.snd; · exact times (h.later hh) (ih _ (by omega) hx)
   rw [ show k.snd=0 from (by omega),hv,mul_one ]; exact h.later hh
end Weight
end YM.FVAAlt2.Mass
