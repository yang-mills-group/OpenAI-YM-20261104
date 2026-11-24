import YM.MSbar.Tonic.Loan
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tonic
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{c f:Side}{S:StepData c f}
local notation "J"=> Positions (Primary c G)
local notation "X"=> Primary c G
local notation "Q"=> Config G f
variable (β t:ℝ)(U:Config G f)(M:Config G c)(v:S.Choices)
local notation "B₀"=> tribe S β t U v
local notation "Φ"=> wing S U v
variable (x:Positions (Primary c G))(L:List (Primary c G))(i j:Primary c G)(e:Bond c)
variable (hc:S.patch.Branches S.kernel G)
local notation "H"=>prior G f
include hc
variable (R: Rep G f)(τ A B C D:ℝ)(hR:R.Lawful τ A B C D)
-- density old milk U-term derivative `S likelihood`.
local notation "W"=> fun x:J=> postcard G c t x
local notation "i!"=>R.eval
local notation "q!"=> lid S β t G R v
include hR
variable (hβ:β=R.beta)(hs:∀ U, 0 < R.eval U)
include hs
local notation "Z!"=>rave S β t R L x
open Heath Heath.Stock Heath.Cottage Next.Fluctuations ConnectedActivityE6 Bulk
variable (F:Forest S.ratio)
local notation "Xc"=> Heath.canoe
variable (I Y: Support f)(J': Voice G)(p: Palisade) (ν:Positions (Key F G)){a b r K:ℝ}{n q j:ℕ} (g: Clear G J')
local notation "V₀"=> W x
local notation "Θ"=> hotel F I Y J' V₀ ν a b
local notation "z"=> chambers F Y J' V₀ ν
variable (hP: Posture p J' F a b r K n q I Y (t • x) ν R.p) (ht:∀ i∈L, S.ratio.embed (Measuring.chart c G i) ∈ I)
variable (hp: Picked G S F K)
local notation "m!"=> woolModel F I J' R Y v V₀ ν a b
local notation "g!"=> Rota.resample F (board F I) (woolModel F I J' R Y v V₀ ν a b) (hotel F I Y J' V₀ ν a b)
local notation "P"=> Bulk.expect S R V₀
variable {ε₀ ε K₀ V' s s':ℝ}
omit hc hR hs
variable {s₁ s₂ s₃ s₄ s₅:ℝ}
lemma modest (k: Config G c)(hl:Bulk.Admitted k R S τ A C B D)(T: Set (Config G f))(hT:MeasurableSet T)(f':Config G f→ℝ)(hE:Envelope f') (y y' q:ℝ)(hz: ∀ i∈T,|f' i| ≤ y)(hh: ∀ i∉T,|f' i|≤ y')(hg:chance S R k Tᶜ ≤ q) (hv:0 ≤ y)(hw:0≤ y') : |Bulk.expect S R k f'| ≤ y+q*y':=by
     let g(X'):=Bulk.expect S R k X'; let f:=(spec Tᶜ); let h(x:Q):= y+y'*f x
     have hh'(i):|f' i|≤h i:=by
        by_cases hx:i∈T; · simpa [h,f,spec,Set.indicator_apply,hx] using hz i hx
        apply (hh i hx).trans; unfold h f; rw [show spec Tᶜ i= (1:ℝ) from Set.indicator_of_mem hx _,mul_one]; exact le_add_of_nonneg_left hv
     let f₀:=h; have hf:RG.Envelope (y' •f):=(RG.Envelope.const _).mul (show Envelope f from by
            have hx(T:Set Q)(he:MeasurableSet T):Envelope (spec T):= Envelope.piece he (Envelope.const _) (Envelope.const _)
            exact hx (Tᶜ) hT.compl);
     have hx :∀ u:Config G _→ℝ,Envelope u→u≤h → g u≤g h:= fun u hu hv=> nn k hl ((Envelope.const y).add hf) hu hv
     have hi : g h=y+y'*chance S R k Tᶜ:= by
        rw [show g h=y+g (y' • f) from ?_]; rotate_left; · apply (e_sum k hl (Envelope.const y) hf).trans (congr_arg (·+_) (e_const k hl _));
        rw [show g (y' •f)=_ from e_mul k y']; rfl -- order
     have hp: g h≤ y+q*y':=by rw [hi]; exact add_le_add_right ((mul_le_mul_of_nonneg_left hg hw).trans_eq (mul_comm ..)) _
     apply abs_le.mpr; refine ⟨?_,(hx _ hE (fun i=>(le_abs_self _).trans (hh' i))).trans hp⟩
     have ht := hx _ hE.neg (fun i=>(neg_le_abs (f' i)).trans (hh' i)); have he : g ((-1:ℝ) • f')= -g f':= (e_mul k (-1 :ℝ)).trans (by change -1*g f'=_; ring)
     have hu: -g f'≤ y+q*y' := he ▸ (le_trans ?_ hp : g ((-1:ℝ) • f')≤y+q*y'); · change - (y+q*y')≤ g f'; linarith
     exact (Eq.trans_le (congr_arg g (show (-1:ℝ) • f'= (fun i=> -f' i) from funext (fun i=>neg_one_mul (f' i)))) ht)
include hs hβ hc hR ht hP hp g
variable (hZ : Rota R (postcard G c t x) (youth F Y) F (board F I) (hotel F I Y J' (postcard G c t x) ν a b) (woolModel F I J' R Y v (postcard G c t x) ν a b) s₁ s₂)
include hZ
noncomputable def witness (S:StepData c f)(R:Rep G f)(β t:ℝ)(x:Positions (Primary c G))(L:List (Primary c G))(T:Set (Config G f)) : Config G f→ℝ:=T.indicator (rave S β t R L x)
local notation "p!"=> PPress S β t R x
lemma motion {p':ℕ}(δ ε c' y e:ℝ)(hq:PriceR G p' K₀)(hK:sizeP L.length (glow S.kernel p' β K₀ G)≤ y)(hh:shade G*|t| *‖x‖ ≤1)(hu : 0 ≤ ε)(hx: |t| ≤1)(hl:L.length ≤ p') (he: chance S R (postcard G c t x) Θᶜ ≤ δ)
      (hX:Loan.Tact F I Θ m! (youth F Y) R (postcard G c t x) (2*y) e)
      (hv:∀ U∈Θ, |(g! (Set.indicator Θ (rave S β t R L x))) U-c'| ≤ ε) : |buoy (PPress S β t R) x L/PPress S β t R x-c'| ≤ 2*e+y*δ+(ε+δ*|c'|):=by
      let Ω:= V₀; let S':=(hotel F I Y J' V₀ ν a b); let f0:=rave S β t R L x; let T':= Set.indicator S' f0; have hs' :=S.isKernel hc R.beta; have ht': Bulk.Admitted V₀ R S τ A C B D :=⟨hR,fun _=>(hs ..).le,Progress.DirectedRecipe.push_strict S R.beta hc hs ((R.envelope hR).integrable _) _, hs'⟩; have hi:=hZ.reforms
      let hpU : ∀ U:Q,|rave S β t R L x U|≤ y:=fun U=> (lust β t x L hc R τ A B C D hR hs hq hx hl hh _).trans hK
      have ha:0 ≤ y:=(abs_nonneg _).trans (hpU 1); have hm:Envelope f0:= ⟨stipend β t x L hc R τ A B C D hR hs,_,hpU⟩
      have hY : GaugeLocal S (youth F Y) T':=scopeY β t x L hc R τ A B C D hR hs F I Y J' p ν g hP ht hp hm v -- args
      let Z:=g! T'; obtain ⟨h₀,HX,hU⟩:=Loan.terms τ A B C D F I _ ht' hZ T' hY (fun U=>by
          change |Set.indicator S' f0 U|≤y; by_cases hh':U∈S'; rw [Set.indicator_of_mem hh']; exact hpU U; rw [Set.indicator_of_notMem hh',abs_zero];exact ha) hX
      have hi'(B B' : Q→ℝ)(h:Envelope B)(g:Envelope B'): Envelope (B-B')∧ (P (B-B'))=P B- P B':=by
          let z':= (-1:ℝ) •B'; have hz:B-B'=B+z':=by unfold z'; simp [sub_eq_add_neg]
          rw [hz]; have hy:Envelope z':=(Envelope.const _).mul g; refine ⟨h.add hy, (e_sum V₀ ht' h hy).trans ?_⟩; rw [show P z'=_ from e_mul _ (-1:ℝ)]; ring
      have hΔ: |P f0-P T'| ≤ y*δ:=by
           have hh:= hi' f0 T' hm hY.currency; have hx:=modest R τ A B C D Ω ht' S' hi.from_here _ hh.1 0 y δ (fun i hi=>by change |f0 i-T' i|≤0; rw [show T' i=f0 i from Set.indicator_of_mem hi _,sub_self,abs_zero]) (fun i hi=>by change |f0 i-T' i|≤ y; rw [show T' i=0 from Set.indicator_of_notMem hi _,sub_zero]; exact hpU i) he le_rfl ha; rw [show _-_=_ from hh.2.symm,mul_comm y δ]; simpa using hx -- omega
      let k:Q→ℝ:=fun _ => c'; have hΨ: |P Z-c'| ≤ ε+δ*|c'|:=by
           obtain ⟨hx,hH⟩:= hi' Z k h₀ (Envelope.const _); nth_rw 1 [← e_const V₀ ht' c']; rw [← show P _= P Z-P k from hH]; apply modest R τ A B C D Ω ht' S' hi.from_here _ hx ε |c'| δ hv _ he hu (abs_nonneg _); intro i hi; change |Z i-c'| ≤ _; rw [show Z i=0 from HX i hi]; simp
      have hz:|P T'-P Z| ≤2*e := by rw [abs_sub_comm]; exact hU
      rw [← spec_r β t x L hc R τ A B C D hR hβ hs]; change |P f0 - c'| ≤ _; apply (abs_sub_le _ (P Z) _).trans; apply add_le_add _ hΨ; exact (abs_sub_le _ (P T') _).trans ((add_le_add hΔ hz).trans_eq (add_comm ..))
end YM.MSbar.Tonic
