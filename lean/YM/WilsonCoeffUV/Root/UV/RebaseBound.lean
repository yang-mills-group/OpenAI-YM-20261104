import YM.WilsonCoeffUV.Root.UV.InverseCost
/-!
# Reexpression windows. Step and inverse bounds at any window read in either endpoint coupling. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V α β:Type*}{r h D l e j k a N M m b i q:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{s t t' A B C δ σ γ S O v:ℝ}
variable {E W U' V':Credit}{T:SectionData F}{p:h<D}
lemma reelQuote (A B: Cost)(i:ℕ): coeff i (Bank.reel A B)= ∑ j∈Finset.range (i+1), coeff j B * coeff (i-j) (A^j):=by
    rw [(filtered (show constantCoeff (Bank.reel A PowerSeries.X)=0 by rw [reel_X]; simp) (shave B (i+1))) i i.lt_succ_self,map_sum,map_sum]; apply Finset.sum_congr rfl; intro j hj; rw [map_mul (Bank.reel A),map_pow (Bank.reel A),reel_X,reel_C,mul_pow,←mul_assoc, coeff_mul_X_pow',if_pos (by have hh:= Finset.mem_range.mp hj; omega),coeff_C_mul]
lemma reelClips {A B P Q:U→Cost}{x θ:U→ℝ}(h:Brite x θ)(p:∀ j≤ i,Weft x θ A B j)(q:∀ j≤ i,Weft x θ P Q j): Weft x θ (fun i=> Bank.reel (A i) (P i)) (fun i=> Bank.reel (B i) (Q i)) i:=by
    unfold Weft; simp only [reelQuote]; apply clips.sum h; intro j hj; have ht:= Finset.mem_range.mp hj; exact (q j (by omega)).mul (show Weft x θ (fun i=> A i^j) (fun i=> B i^j) (i-j) from clipped_pow h j (fun j hj=>p j (by omega)))
structure CourseS (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(C D' E:Credit) where
    robe : ChorusLine H T p e C D' E
    I: WindowS G (e+1) C
    peace : I.robe=robe.arch.V
namespace CourseS
variable (M:CourseS H T p e E W U')
abbrev spur:= M.I.base
abbrev length:= M.I.span
abbrev tip:= M.spur+ M.length
abbrev root : M.robe.arch.V.anchor ≤ M.spur:= M.peace ▸ M.I.root
abbrev far : M.tip≤ M.I.b:= M.I.endS
abbrev vols:= M.robe.arch.V
abbrev Age:= M.I.Age
abbrev cab:= M.I.cab
lemma crop (L:WindowS G (e+1) E)(n N:ℕ)(h:L.base≤ n)(hx:n+N ≤ L.base+L.span): L.robe.y n≤ L.Age := by rw [show n= L.base+(n-L.base) by omega]; exact L.covers (by omega)
-- beware Age when when `Window interval subset` not start. R.age gives monotone upper scale.
def clipW (v:N+ i ≤M.length) := ({
                                      robe:= M.I.robe
                                      base:= M.I.base+N
                                      span:= i
                                      n:= M.I.n
                                      N:= M.I.N
                                      b:= M.I.b
                                      root:= by have h:= M.I.root; omega
                                      endS:= by have h:= M.I.endS; change N+i ≤ M.I.span at v; omega
                                      hd:= M.I.hd
                                      hg:= M.I.hg } : WindowS G (e+1) E)
lemma cup (p:N+i ≤ M.length): (M.clipW p).Age≤ M.Age ∧ (M.clipW p).cab ≤ M.cab :=by
    let S:=M.I.base; let a:=M.I.robe; let n':=M.length
    have hv:a.y (S+N)≤a.y S+(a.draws.S.scale (S+N)-a.draws.S.scale S):=a.age _ _ M.I.root (by omega); have hp:i≤n':=by unfold n'; omega
    have hu:S+N+i≤M.tip:=by change S+N+i≤ S+M.length; omega
    refine ⟨?_ ,PathCost.narrow M.I.robe.draws.S hu _⟩; change a.y (S+N)+(a.draws.S.scale (S+N+i)- a.draws.S.scale (S+N))+i ≤ a.y S+(a.draws.S.scale M.tip-a.draws.S.scale S)+n'; linarith [show a.draws.S.scale (S+N+i) ≤ _ from scales a.draws.S hu, show (i:ℝ)≤ n' from Nat.cast_le.mpr hp]
end CourseS
abbrev Chars (F:Frame G h)(C:Cost): Coil F→+* Coil F:= (Bank.reel C).mapMatrix
lemma maxStroke (C:Cost)(F:Frame G h) (P:Coil F) : lineS (Chars F C P) 0=lineS P 0:= by ext1 s v; change coeff 0 (Bank.reel C (P s v))= _; rw [reelQuote]; simp [lineS]
lemma Chars.glide {x θ:U→ℝ}(p:Brite x θ){P Q: U→Coil F} {A B:U→ Cost}(h:∀ i≤ e,Weft x θ A B i)(e':∀ i≤e,CreditsS x θ (fun n=>lineS (P n) i) (fun n=>lineS (Q n) i)): CreditsS x θ (fun n=>lineS (Chars F (A n) (P n)) e) (fun n=> lineS (Chars F (B n) (Q n)) e):=by
    intro i j; exact reelClips (P:=fun n=> P n i j) (Q:= fun n=>Q n i j) p h (fun v hv => e' v hv i j)
abbrev CourseB (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(E W C':Credit): Brite (CourseS.Age (H:=H) (T:=T) (p:=p) (e:=e) (E:=E) (W:=W) (U':=C')) CourseS.cab:= ⟨fun i=>i.I.warm,fun _=> (trail_pos ..).le⟩

lemma clips.crop {x y:U→ℝ}{z θ:V→ℝ}{P Q:V→α}[NormedAddCommGroup α](f: U→ V)(h:clips z θ P Q)(p:Brite z θ)(q:Brite x y)(hv:∀ i,z (f i)≤ x i)(hq:∀ i,θ (f i) ≤ y i):clips x y (P∘f) (Q∘f):=by
    obtain ⟨d,A,b,u⟩:= h; exact ⟨d,A,b,fun i=>(((u (f i)).wide (hq i)).lift (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (p.large _)) (hv i) _) b) (q.dist _))⟩

section
-- use Bool for demand.
variable {C':Credit}
lemma windowBounds (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(E W C':Credit) (v:i≤e): let X:=CourseS.length (H:=H) (T:=T) (p:=p) (e:=e) (E:=E) (W:=W) (U':=C'); let y:= rub X CourseS.Age; let θ:=rub X CourseS.cab
   CreditsS y θ (fun u=>lineS (Jacob u.cargo.vols.draws u.cargo.vols.paid T p u.cargo.I.n (u.cargo.spur+u.coin)) i) (fun u=>lineS (Jacob u.cargo.vols.draws u.cargo.vols.paid T p u.cargo.I.N (u.cargo.spur+u.coin)) i) := by
   intro X y θ j z; let C:= robePort H T p e E W C'; refine ⟨C.d,C.x,zero_le_one.trans C.good,fun ⟨a,k,hq⟩=>?_⟩
   let V:= a.robe.arch; let R:=V.V; have hg: k<a.length:=hq
   have hv : a.spur+k<a.tip:= by unfold CourseS.tip; omega
   have hm:a.spur+k < a.I.b:= hv.trans_le a.far
   have hx:R.anchor≤ a.spur+k:= by apply le_trans a.root; omega
   have he:R.tempC (a.spur+k) a.I.b≤ a.I.cab:=by unfold WindowS.cab; rw [a.peace]; exact PathCost.narrow R.draws.S hv.le _
   have hu:R.y (a.spur+k)≤ a.Age:= by rw [← show a.I.robe=R from a.peace]; exact a.I.covers hg.le
   exact (((opening a.robe hx hm a.I.hd a.I.hg j z v).lift (C.elder (R.depth _ hx) hu) (trail_pos ..).le).wide he)
-- scalar clipping in either direction by window subset; endpoint choice consistent.
lemma edgeC (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(E W C':Credit)(v:i≤e)(b:Bool): let X:=CourseS.length (H:=H) (T:=T) (p:=p) (e:=e) (E:=E) (W:=W) (U':=C'); let y:= rub X CourseS.Age; let θ:=rub X CourseS.cab; let F (j:Jag X)(N):= if b then relativeC j.cargo.vols.draws j.cargo.vols.paid N (j.cargo.spur+j.coin) (j.cargo.length-j.coin) else relativeF j.cargo.vols.draws j.cargo.vols.paid N j.cargo.spur j.coin; Weft y θ (fun i=>F i i.cargo.I.n) (fun i=> F i i.cargo.I.N) i:=by
    intro X y θ V
    have hc := (CourseB H T p e E W C'); have he : Brite y θ:= ⟨fun i=>hc.large _,fun i=>hc.dist _⟩
    cases b
    · unfold V; simp only [Bool.false_eq_true,↓reduceIte]; unfold Weft
      let f (i:Jag X) := i.cargo.clipW (show 0+i.coin≤ i.cargo.length from by rw [Nat.zero_add]; exact i.credit.le); let R(v:WindowS G (e+1) E):= relativeF v.robe.draws v.robe.paid
      have hp:= clips.crop f (ascend G (e+1) i E (by omega)) (WindowS.payments G (e+1) E) he (fun i=> (i.cargo.cup _).1) (fun i=>(i.cargo.cup _).2)
      simpa only [f,  Function.comp_def,CourseS.clipW, CourseS.peace,Nat.add_zero] using hp
    unfold V; simp only [↓reduceIte]; unfold Weft
    have hh (i:Jag X): i.coin+(i.cargo.length-i.coin)≤ i.cargo.length:= by rw [Nat.add_sub_of_le (show i.coin≤ i.cargo.length from i.credit.le)]
    let f (i:Jag X) := i.cargo.clipW (hh i)
    have hp:= clips.crop f (Bank.descend G (e+1) i E (by omega)) (WindowS.payments G (e+1) E) he (fun i=> (i.cargo.cup _).1) (fun i=>(i.cargo.cup _).2)
    simpa only [f,  Function.comp_def, CourseS.clipW, CourseS.peace] using hp
end
end YM.WilsonCoeffUV.Cosmos
