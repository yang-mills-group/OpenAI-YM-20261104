import YM.WilsonCoeffUV.Winding.Stamp
/-! # Enrollment. Q step/Bulk (& optional exact nibs nearby).
Taxes can depend on common earlier P.w calibration but not action/mark payments.
Marks purchased for any size in same Z subset. Extra width cuts for alias
outputs (if needed) may again use arbitrary post cost at these shapes.
-/
set_option autoImplicit false
set_option maxHeartbeats 560000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Wheel Wheel.Mark Cosmos Mer Function Filter Lattice RG Embroider Soil Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent AnalyticNext.QuarticMatch.Sheets PowerSeries Bank.Mosaic Bank.Carp
open Realm PathCost
open scoped Topology BigOperators
variable {n L:Side}{ι U X α β T:Type}{V:Type}{G:Gauge}{D k:ι→ℕ}{Ñ:ChartRatio G}{m N i j r e a l f:ℕ}{s A B C W t q :ℝ}
variable {J Z S:Finset ι}{p:ι→Cover}{E H:Credit}{Q:Realm G (e+1) E}{R: Levels G}{v: m<N}

-- Shelf for bulk, horizon e applicant uses the F+1 PS release
abbrev coil0 (A:Levels G)(Ñ:ChartRatio G)(m N:ℕ)(n:Side):= unripe A Ñ N m (emera (actionW A Ñ N (m+1))) n
lemma purchaseW (G:Gauge)(e i r:ℕ)(h:i≤ e)(H E:Credit) (u:Gear G→ℝ)(hu:∀ I,0<u I): ∃ (s c:Gear G→ℝ)(U:Credit), (∀ I,0<s I ∧ (s I)⁻¹≤c I) ∧
     ∀ Q: Realm G (e+1) E,∀ m N n (p:Q.anchor≤m) (_:m < N), let I:= (Q.mint m p).gear; c I ≤ Q.cash H m →
       Sight (coil0 Q.draws Q.paid m N n i r) (freshet Q.draws Q.paid N m i r) (s I) (Q.cash U m):=by
    obtain ⟨d,hD⟩:= windingVault G e i r h; choose s a f x g using hD
    classical
    let F (I:Gear G):= I.patch.Branches I.kernel G ∧ LocalRatio I.angle; let D (I:Gear G) (p:F I):= aerie (u I) I e (hu I) p.1 p.2
    let t(I:Gear G):= if p:F I then s (D I p) else 1; let C (I:Gear G):= if p:F I then max (admissionA I e) (a (D I p)) else 0; let v (I:Gear G):=max (C I) (t I)⁻¹
    let V:=H.prodC ((H.prodC (costXV G e E)).powC d)
    refine ⟨t,v,V,fun I=> ⟨?_,le_max_right ..⟩,?_⟩; · unfold t; split; exact f _; positivity
    intro Q m N n p y I c
    have ht:F I:= ⟨(Q.draws.blocks m 0).branches,Q.green⟩; let P:= cloVent Q m N n p y (u I) (hu I); let w:= Q.cash (costXV G e E) m; have hw:1≤ w:= Credit.purchase _ (Q.depth _ p)
    have hh:max (admissionA I e) (a (D I ht))≤ Q.cash H m:= by apply le_trans _ c; apply le_trans _ (le_max_left ..); unfold C; rw [dif_pos ht]
    unfold t; rw [dif_pos ht]; have he:P.coin=admissionA I e*w:=rfl
    apply (g _ P).more; rw [he]; unfold cash V; rw [Credit.products,Credit.power,Credit.products]
    exact mul_le_mul (le_trans (le_max_right ..) hh) (pow_le_pow_left₀ (he ▸ (zero_le_one.trans P.paid)) (mul_le_mul_of_nonneg_right (le_trans (le_max_left ..) hh) (zero_le_one.trans hw)) _) (pow_nonneg (he ▸ (zero_le_one.trans P.paid)) _) (zero_le_one.trans (Credit.purchase _ (Q.depth _ p)))

variable [DecidableEq ι]
abbrev coilH (Q:Levels G)(Ñ:ChartRatio G)(m N:ℕ)(n:Side)(K:family G D)(k:ι→ℕ)(C:Cost):=let P:=loose Q m; mist (stepAt P Q.clock.kernel n) (xree P Q.clock.kernel n) (freeForms Q N (m+1)) (roam Q N m n) Ñ (emera (actionW Q Ñ N (m+1)) (n*P.L)) (repaint K) C k

theorem pledges (G:Gauge)(e i r:ℕ)(h:i ≤ e)(H E: Credit)(u:Gear G→ℝ)(hu:∀ I,0<u I)
    (g:J⊆Z)(D k:ι→ℕ)
    : ∃ (s c:Gear G→ℝ)(U:Credit),(∀ I,0<s I ∧ (s I)⁻¹≤c I) ∧
    ∀ Q: Realm G (e+1) E,∀ m N n (p:Q.anchor≤ m)(_h:m<N),
    let I:= (Q.mint m p).gear; c I ≤ Q.cash H m → ∀ K:family G D, Eu k K → K ∅=0 → ∀ (y:ι→Cover) (z:ι→Site (loose Q.draws m).L) A,
    0≤A → safeB (chartIn (loose Q.draws m) y z) K Z e (u I) A →
      MarkU y J (coilH Q.draws Q.paid m N n K k (ratioHigh Q.draws Q.paid N m) J i r) ((logO Q.draws Q.paid m N K k J).2 i r) (s I) (Q.cash U m*A^J.card):=by
    obtain ⟨d,H'⟩:= qLocal_mark (G:=G) (k:=k) (D:=D) e i r h J Z g; obtain ⟨z,V⟩:= rimMoney G i r e h; choose C s b x f using H'; choose T he ht using V
    classical
    let F (I:Gear G):Prop:= I.patch.Branches I.kernel G ∧ LocalRatio I.angle; let D' (I:Gear G) (p:F I):= aerie (u I) I e (hu I) p.1 p.2
    let t (I:Gear G):=if p:F I then s (D' I p) else 1
    let L (I:Gear G):= if p:F I then max (max (T I) (admissionA I e)) (max (C (D' I p)) (diamond G e (mass k Z) (u I))) else 0
    let C' (I:Gear G):=max (L I) (t I)⁻¹; let P:=costXV G e E; let Wm0:=H.prodC ((H.prodC P).powC d); let U:=(Wm0.prodC (H.powC J.card)).prodC (H.prodC (P.powC z))
    refine ⟨t,C',U,fun I=>⟨?_,le_max_right ..⟩,?_⟩; · unfold t; split; exact x _; positivity
    intro Q m N n p v I B K R hK y w A hA hB
    have hv: F I:=⟨(Q.draws.blocks m 0).branches,Q.green⟩; let Z' := D' I hv
    unfold t; rw [dif_pos hv,← flowBolt Q Z K m N p v _ (hu I) y w hK R A hA hB n J]
    let X:= flowOne Q Z K m N p v _ (hu I) y w hK R A hA hB n; let W:=Q.cash H m; let b0:= Q.cash P m; let U₀:= ReelTime Q (i:=e) le_rfl p v (le_refl N) (le_refl N); let T':= rimJ U₀.P.moving i r; have hh:= f _ X U₀.P.moving
    let a':= C Z'; let u':=diamond G e (mass k Z) (u I)
    have he:A* (0:ℝ) ≤ A:= by simp [hA]
    have hz:max (max (T I) (admissionA I e)) (max a' u')≤ W:=by refine le_trans ?_ ((le_max_left ..).trans B); unfold L; rw [dif_pos hv]
    obtain ⟨⟨h',g'⟩,b',c'⟩:= And.intro (max_le_iff.mp (max_le_iff.mp hz).1) (max_le_iff.mp (max_le_iff.mp hz).2)
    have hw:1≤W:=Credit.purchase _ (Q.depth _ p)
    have hu':1≤u':=diamond_nn G (hu I)
    have hb':1≤b0:=U₀.rich
    have ht':T'≤W*b0^z:= (ht I U₀).trans (mul_le_mul_of_nonneg_right h' (pow_nonneg (zero_le_one.trans hb') _))
    have hT:0 ≤ T':= Finset.sum_nonneg (f:=fun j=> ‖PowerSeries.coeff (i-j) (U₀.P.moving^j*(U₀.P.moving⁻¹)^r)‖) (fun i _=>norm_nonneg _)
    apply hh.more; rw [show X.A = diamond G e (mass k Z) (u I)*A from rfl]
    have ha:1≤admissionA I e:=admissionSeal I; change a'*(admissionA I e*b0)^d*(u'*A)^J.card*T' ≤ _
    unfold cash U Wm0; rw [Credit.products,Credit.products,Credit.products,Credit.products,Credit.power,Credit.power,Credit.power,Credit.products]; apply le_trans (b:=W*(W*b0)^d*(W*A)^J.card*(W*b0^z)); · gcongr
    change _≤W*(W*b0)^d*W^J.card*(W*b0^z)*A^J.card; rw [mul_pow]; exact le_of_eq (by ring)
end YM.WilsonCoeffUV.Winding
