import YM.XSpace.Sonar

/-!
# Isothermal comparison on leading operators: from the expanding quotient to exact
Wick-subtraction matches on the cover
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Encore
open Lattice Sail Litter Trace Chart2 JetGauge MvPolynomial Next.Rank.Normal Function Filter Set Finsupp Contraction Further.FreeCovariance.KP Outline Comets Comets.Input Asymptotics Expense
open scoped Topology BigOperators
variable {G:Gauge} {H:Source.Hol G} {d e:ℕ} {R:Period}
lemma uniform_zero (A:St (Per R.side) G) (h:∀ v:Four (Per R.side)→G.Color, D (grad v) A=0)(T:R.Tree)(K:Meet G R): E (treeCov T G) A=E (wide K) A:=by
  let Y:PowerSeries (St (Per R.side) G):= PowerSeries.X * PowerSeries.C A
  have hz : PowerSeries.constantCoeff Y=0:=by simp [Y]
  have hs : PowerSeries.coeff 1 Y=A:=by unfold Y; rw [PowerSeries.coeff_one_mul]; simp
  have hw : price1 (R:=R) Y=A:=by simp only [price1,hs,hz,mul_zero,sub_zero]
  have he: Good (R:=R) Y := by constructor <;> intros <;> simp only [hz,hs,map_zero,h,neg_zero]
  conv => lhs; arg 2; rw [← hw]
  rw [← setting T K he,hw]

variable {Z:Type*} {L: Filter Z} {ι: Type*} {Dgr:ι→ℕ} (S:∀ i:ι,Survey G H (Dgr i))(U:ι→Labels.Pol G)(s:Finset ι)
def zeroReading (x:ι→Cover) : ℂ:= E (duskCov G) (PowerSeries.constantCoeff (crop s S U x))
lemma expense_zero (T:R.Tree)(x:ι→R.Sites) : PowerSeries.constantCoeff (Bare.normalized T G (∏ i∈s,Bare.raw T (S i) (x i) (U i)))=E (Outline.dawn G R).grant (PowerSeries.constantCoeff (crop s S U x)):=by
  rw [Bare.leading,(reconstruct_product T s (fun i _=> reconstruct_toy T (S i) (x i) (U i))).1, transfers]; change E _ _=_; apply uniform_zero
  intro v; rw [map_prod]; classical
  induction s using Finset.induction_on with | empty => simp | insert i s h ih=> rw [Finset.prod_insert h,(D (grad v)).leibniz, ih,show D _ (PowerSeries.constantCoeff _)= _ from quench (S i) (x i) (U i) v]; simp

lemma zeroFlat (p:Z→Mesh)(X:Stretched L p)(z:Z→ι→Cover)(o:Z→Cover)(hh:∃ k:ℕ,∃ r:Z→ℕ, (∀ᶠ i in L,Tall (p i).p (o i)∧∀ j,reach (z i j-o i)≤r i)∧ (fun i=> (r i:ℝ))=O[L]fun i=>(a p i)⁻¹^k)(T:∀ i,(p i).p.Tree):
    Cross.Blank L p (fun i=> PowerSeries.constantCoeff (Bare.normalized (T i) G (∏ j∈s, Bare.raw (T i) (S j) (wrap (p i).p.side (z i j)) (U j)))- zeroReading S U s (z i)):= by
  obtain ⟨k,r,hr,hh⟩:=hh; obtain ⟨A,hA,HA⟩:=hh.exists_pos; obtain ⟨C,hC,H⟩:=(arc (PowerSeries.constantCoeff (polynomials s S U))).1
  intro n; apply IsBigO.of_bound (C*(1+A)); filter_upwards [HA.bound,hr,(X.pay (k+n)).eventually_ge_atTop 1, X.smaller] with i hi hv hx ht; have hj:= expense_zero S U s (T i) (fun j=>wrap (p i).p.side (z i j)); rw [hj, zeroReading, (steam s S U (Outline.dusk G) (z i)).1, (steam s S U (Outline.dawn G (p i).p) _).1]
  apply le_trans (H (p i).p (o i) hv.1 (r i) (z i) hv.2)
  set b:= a p i; have h0:0<b:=actual p i; have hp:(((p i).p.side.val:ℕ):ℝ)=sides p i:=rfl; have hn:=counted p i
  rw [budget,hp,Real.norm_of_nonneg (pow_nonneg h0.le n),mul_assoc]; gcongr C*?_
  rw [Real.norm_of_nonneg (by positivity),(Real.norm_of_nonneg (by positivity : 0≤b⁻¹^k))] at hi; rw [div_le_iff₀ hn]; change b^_*_≥1 at hx; rw [pow_add] at hx
  have he:1≤b⁻¹ ^ k:= one_le_pow₀ (one_le_inv₀ h0|>.2 ht)
  have hh:b⁻¹^k ≤ b^n * sides p i:= by rw [inv_pow,inv_le_iff_one_le_mul₀ (pow_pos h0 _)]; linarith [mul_assoc (b^k) (b^n) (sides p i)]
  change _≤(1+A)*b^n*_; nlinarith

variable (σ:Survey G H d)
def reel (x:Cover) : Labels.Pol G→ₐ[ℂ] St ℤ G:= exchange (fun i=> complexCode G (displace x (ping σ i)))
lemma tuned (x:Cover)(u:Labels.Pol G) : p0 σ x u=reel σ x u:=by
  unfold p0; induction u using MvPolynomial.induction_on with | C a=> simp [toy, PowerSeries.algebraMap_apply, MvPolynomial.algebraMap_eq,reel] | add p q hp hq=> simp only [map_add,hp,hq] | mul_X p i h=> rw [map_mul,map_mul,map_mul,h]; congr 1; unfold reel toy; rw [exchange_x, MvPolynomial.aeval_X,constant_knit]; apply pulses

private lemma mean_match {I:Type*}(R:JetGauge.Cov I)(u v:I→₀ℂ): E R (glyph u * glyph v)=treats R u v:=by
  classical
  let f:Unit→I→₀ℂ:= fun _=>u; let g:= ![u,v]; have ht : treats R u v=(scope g R).cov 0 1:=rfl
  have he:= wets g R (0:I→ℂ) (X 0 * X 1); rw [map_mul,exchange_x,exchange_x] at he; rw [ht]; apply he.trans; rw [show reads g 0=0 from funext fun i=>by simp [reads], blended,slit_X];simp [blend_components]

lemma self_match (x: Cover):scope (fun i=> complexCode G (displace x (ping σ i))) (duskCov G)=σ.selfCov 1:=by
  apply Symmetric.ext; funext i j; change treats _ _ _ =_; rw [heard,meter_serves]; let A :Run:= ⟨3,by decide,1,⟨4,by decide,by decide⟩,by decide,by decide⟩; let p:=A.step; let g:=fun n:ℕ=>(p n).p; have S:Stretched atTop p:=Stretched.runs A; let z n:Cover:=fun _=> (nodes (p n):ℤ)/4; have hz:Cross.Centered atTop p z:=by
    filter_upwards [S.horizon.eventually_ge_atTop 32] with n hn; have hp:32≤nodes (p n):=by change 32≤ (nodes (p n):ℝ) at hn; exact_mod_cast hn
    unfold z; omega
  let V (n:ℕ): (g n).Tree:= Period.standardTree _; let y n:= wrap (g n).side (z n); let Y : Labels.Pol G:=X i*X j
  let f n:= PowerSeries.constantCoeff (Bare.normalized (V n) G (Bare.raw (V n) σ (y n) Y))
  have hq:Tendsto f atTop (𝓝 (handshake (ping σ i) (ping σ j):ℂ)) := by
    have hr:= zeroFlat (fun _:Unit=> σ) (fun _=>Y) {()} p S (fun i (_:Unit)=> z i) z (by refine ⟨0,fun _=>0,hz.mono (fun i hi=> ⟨Probes.seams _ _ hi.1 hi.2,fun j=>by simp [Sail.reach_zero]⟩),?_⟩; simp only [Nat.cast_zero]; exact isBigO_zero _ _) V 1
    simp only [Finset.prod_singleton,zeroReading,crop] at hr; change (fun i'=>f i'- E (duskCov G) (p0 σ (z i') Y))=O[atTop] _ at hr
    simp_rw [tuned σ _ Y, Y,map_mul,reel,exchange_x,mean_match,heard,meter_serves,pow_one] at hr
    have ht:= (hr.trans_tendsto S.endpt).add (show Tendsto (fun _:ℕ=> (handshake (ping σ i) (ping σ j):ℂ)) atTop _ from tendsto_const_nhds (x:= (handshake (ping σ i) (ping σ j):ℂ))); rw [zero_add] at ht; exact ht.congr fun k=> sub_add_cancel ..
  apply tendsto_nhds_unique hq; rw [Cross.sleeps]; unfold f Y y; simp_rw [Bare.leading,Cross.milk_raw]; change Tendsto (fun k=> E (Bare.Q (V k) G) (exchange _ _)) atTop _; simp_rw [map_mul, exchange_x,mean_match, Cross.reads_position]
  let C n:= Cross.lag (G:=G) (g n) (z n) (z n)+Cross.extra (G:=G) (g n) (z n) (z n); let L:=Cross.readKey σ i; let M:=Cross.readKey σ j
  refine Tendsto.comp (Complex.continuous_ofReal.tendsto _) (show Tendsto (fun n=> Next.Rank.Beamer.mourn L M (C n)) atTop _ from ?_)
  let k n:= C n-Cross.self; have he : ∀ u v, Cross.Blank atTop p (fun n=> k n u v):=fun u v=>fun w=> IsBigO.congr_left ((Cross.contact S z u v w).add (Cross.img S hz hz u v w)) (by intro n; unfold k C; simp only [Pi.add_apply,Pi.sub_apply]; abel)
  have hp:= Cross.pull_blank _ _ (Cross.blossoms σ (Survey.component i)) (Cross.blossoms σ (Survey.component j)) k he 1; simp_rw [pow_one] at hp
  have ht:= (hp.trans_tendsto S.endpt).add (tendsto_const_nhds (x:=Next.Rank.Beamer.mourn L M Cross.self)); rw [zero_add] at ht; apply ht.congr; intro n; change Next.Rank.Beamer.mourn L M (k n)+_= _; unfold Next.Rank.Beamer.mourn k; rw [← map_add]; congr 1; ext z; simp only [Pi.add_apply,Pi.sub_apply,map_sub]; abel
lemma opens (x:Cover)(u:Labels.Label G d): p0 σ x (σ.insertW (-1) u).val = milk (-(duskCov G)) (reel σ x u.val):=by rw [tuned,reel,prepared,scope_neg,self_match,Survey.insertW_val,σ.inverseCov]
end YM.XSpace.Encore
