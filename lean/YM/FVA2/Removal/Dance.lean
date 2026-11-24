import YM.FVA2.Removal.Wires
/-!
 # Even removing a generator on the quotient, on full (not only connected)
 correlations, carries same period-power gain before imposing a super-poly
 growth schedule. Preserve this information at **all** fixed orders by
 allowing spending additional negative powers of spacing.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Removal
open Function Set Filter Finset Metric MeasureTheory Real
open MS MS.Koszul MS.Plane MS.Landau MS.Tone Lattice MS.Land MS.Latch MS.Latch.Job MS.Tide MS.High
open MS.Vane MS.Rake MS.Rake.Geo MS.Vista MS.Vane MS.Fleet MS.Dial
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Engine MS.Puff.SplitP MS.Puff.Actors MS.Puff.Mom MS.Swirl
open scoped Topology ContDiff Interval
variable {I:Type} {l:Filter I}{P:Geo I}{L:I→Side}{V: MS.Vista.Visa I}{μ:ℝ}
variable {x y u v:I→ℂ}
lemma payment_le (P:Geo I)(L:I→Side)(m:ℕ)(i:I): vol P L m i ≤ exp ( m * P.θ i ):= mul_le_of_le_one_right ( exp_pos _|>.le ) ( Real.rpow_le_one_of_one_le_of_nonpos (δ_L L i) (neg_nonpos.mpr mild_p.le) )
lemma cash_le(P:Geo I)(L:I→Side)(m:ℕ)(i:I): cost P L m i≤ 2*exp ((m:ℝ)*P.θ i):= by rw [cost,two_mul]; apply add_le_add _ ( payment_le .. ); apply ( engl P i ).trans; exact one_le_exp ( by have he:= P.room i; positivity )
lemma Vol.passenger (a:Vol l P L x)(b: Total l P L y): Vol l P L ( x*y ):= by
 obtain ⟨C,hC,m,hm⟩:=a; obtain ⟨D,hD,n,hn⟩:=b; refine ⟨ 2*(C*D), by positivity,m+n,?_⟩; filter_upwards [hm,hn] with i hi hq; rw [Pi.mul_apply,norm_mul]; apply (mul_le_mul hi (hq.trans (mul_le_mul_of_nonneg_left (cash_le ..) hD.le)) ( norm_nonneg _ ) (( norm_nonneg _ ).trans hi)).trans_eq; unfold vol; push_cast; rw [add_mul,Real.exp_add]; ring
lemma Vol.bounded (a:Vol l P L x)(b: PeakT l P 0 y): Vol l P L (x*y):= by
 obtain ⟨C,hC,m,hm⟩:=a; obtain ⟨D,hD,hk⟩:=b; refine ⟨ C*D,by positivity,m,?_⟩; filter_upwards [hm,hk] with i hi hq; simp [lake] at hq; rw [Pi.mul_apply,norm_mul]; apply ( mul_le_mul hi hq ( norm_nonneg _ ) ( ( norm_nonneg _ ).trans hi ) ).trans_eq; ring
lemma Vol.ship (a:Vol l P L x)(b:Tight l P L y u): Vol l P L (x*y):= by
 rw [show x*y=x*u+x*(y-u) from (by ring)]; exact ( a.bounded b.1 ).plus ( a.passenger b.2 )
structure Fraction (l:Filter I)(P:Geo I)(L:I→Side)(x y z:I→ℂ): Prop where
 priced: Tight l P L x z
 volume: Vol l P L (x-y)
variable {a b:I→ℂ}
lemma another (a0:Fraction l P L x y a): Tight l P L y a:= by
 refine ⟨a0.priced.1,?_⟩; rw [show y-a=(x-a) + -(x-y) from (by ring)]; exact a0.priced.2.plus a0.volume.covers.neg
lemma Fraction.plus (a0:Fraction l P L x y a)(a1:Fraction l P L u v b): Fraction l P L (x+u) (y+v) (a+b):= ⟨a0.priced.plus a1.priced,by rw [ add_sub_add_comm ]; exact a0.volume.plus a1.volume ⟩
lemma Fraction.join (a0:Fraction l P L x y a)(a1:Fraction l P L u v b): Fraction l P L (x*u) (y*v) (a*b):= ⟨ a0.priced.join a1.priced, by rw [ show x*u-y*v=(x-y)*u+(u-v)*y from (by ring) ]; exact (a0.volume.ship a1.priced).plus ( a1.volume.ship (another a0) ) ⟩
lemma Fraction.constant (s:ℂ): Fraction l P L (fun _=>s) (fun _=>s) (fun _=>s):= ⟨ Tight.constant s,by rw[sub_self];exact Vol.zero ⟩
variable {J W:Type}{f g p:I→J→ℂ}
lemma Fraction.sum (s:Finset J)(hp:∀ j∈s,Fraction l P L (fun i=> f i j) (fun i=>g i j) (fun i=>p i j)): Fraction l P L ( fun i=>∑ j∈s,f i j ) ( fun i=>∑ j∈s,g i j ) ( fun i=>∑ j∈s,p i j ):= by
 classical induction s using Finset.induction_on with| empty=>simp_rw [Finset.sum_empty]; exact constant 0| insert _ s h ih=> simp_rw [Finset.sum_insert h]; exact ( hp _ (by simp) ).plus ( ih fun i hi=> hp i (Finset.mem_insert_of_mem hi ) )
abbrev Budget (l:Filter I)(P:Geo I)(L:I→Side)(x y z:I→J→T ℂ): Prop:= ∀ i n,Fraction l P L (fun j=>x j i n) (fun j=> y j i n) (fun j=> z j i n)
variable {F G U M N A:I→J→ T ℂ}
lemma Budget.times (S: SplitP J)(h:Budget l P L F G U)(hp:Budget l P L M N A): Budget l P L (fun i=> S.Lift (Trunk.core) ( F i ) ( M i ) ) (fun i=>S.Lift Trunk.core ( G i ) ( N i )) (fun i=>S.Lift Trunk.core ( U i ) ( A i )):= by intro x n; simp_rw [ S.loan,Finset.sum_apply ]; exact Fraction.sum _ fun j _=> Fraction.sum ( antidiagonal n ) (fun k _=> Fraction.join ( h j.1 k.1 ) ( hp j.2 k.2 ))
lemma Budget.cheer (S:SplitP J)(h:Budget l P L F G U)(u:J)(n:ℕ): Fraction l P L (fun i=> Cheer Trunk S ( F i ) u n) (fun i=> Cheer Trunk S ( G i ) u n) (fun i=> Cheer Trunk S ( U i ) u n):= by
 have hp(n:ℕ): Budget l P L ( fun i=> (Trunk.stack S).power ( F i ) n ) (fun i=> (Trunk.stack S).power ( G i ) n) (fun i=> (Trunk.stack S).power ( U i ) n):= by induction n with| zero=> intro x j; exact Fraction.constant _| succ _ ih=> exact Budget.times S h ih
 unfold Cheer MS.Puff.Actors.cheers; simp_rw [Finset.sum_apply]; exact Fraction.sum _ fun j _=> Fraction.join (Fraction.constant (MS.Puff.Actors.phase j)) (hp j u n)
open PeakT (ordZ)
lemma Budget.runs [LinearOrder W] (F B C:Terrify W I)(h:∀ (s:Finset W) (k:ℕ), Fraction l P L ( F s k ) ( B s k ) ( C s k )) (s:Finset W)(n:ℕ): Fraction l P L (ordZ F s n) (ordZ B s n) (ordZ C s n):= by
 let Q(t:I)(a:Terrify W I):= fun i n=> a i n t; apply Budget.cheer ( S:=marked W ) ( F:=fun t=> Q t F ) ( G:=fun t=> Q t B ) ( U:=fun t=> Q t C ) _; exact fun i n=> h i n
set_option quotPrecheck false
variable {T:Trial I W}{G:Gauge} {K: Land.Booked (Press.portDeck G)}{S: MS_Data G K}{Y:XSpace.Initialize G}
variable [LinearOrder W] {A:Land.Prescription (Press.portDeck G)}{u : W→Label (Press.portDeck G)}{f z: MS.Fleet.Terrify W I}
lemma MenuCost.full (H:Fit T μ)(hs:MenuCost S Y T A u μ l f z)(s:Finset W)(n:ℕ) : Fraction l T.profile T.side (fare (Label.h∘u) T.profile ( ordZ f ) s n) (fare (Label.h∘u) T.profile ( ordZ z ) s n) (fun i=> tour S u μ ( testP T i ) s n ):= by
 obtain ⟨_,_,_,_,B,_,_,_,_,_,hB,_⟩:= hs.fabric
 have hp:=posed (μ:=μ) T.off H.knit
 have h0(s:Finset W)(n:ℕ) : Fleet.toZ B s n= (fun i=> book S u μ ( testP T i ) s n ):= funext fun i=> Point_t S u μ hp hB i s n
 rw [ ← show ordZ (Fleet.toZ B) s n=(fun i=>tour S u μ ( testP T i ) s n) from funext fun i=> shape_f S u μ hp hB i s n ]; let x:= Label.h ∘ u
 change Fraction l _ _ ( fare x _ _ _ _ ) (fare x _ _ _ _) _
 rw [ ← funext (fun i=> PeakT.ν_norm x (s:=s) ( n:=n ) ( P:=T.profile ) i f ), ← funext (fun i=> PeakT.ν_norm x (s:=s) ( n:=n ) ( P:=T.profile ) i z ) ]; exact Budget.runs _ _ _ (fun s n=> ⟨(h0 s n).symm ▸ ( hs.reaches s n |>.1 ),hs.reaches s n|>.2.2 ⟩ ) s n
end YM.FVA2.Removal
