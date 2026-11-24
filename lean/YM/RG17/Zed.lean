import YM.RG17.Egg
/-!
# At actual F and L and actual Y/m. Reading spatial resolved.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits OPE.Log Extraction Word
open Next.UVStress SharpGram PhysicalNext PhysicalNext.Repeat.Legato Lattice RG Wilson Next.Rank MergeProof Ribbons ManyCopies
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}(R:Run G){S:Table R.family.book}{f: Extraction.Order}{F: Spec.Final R.family f S}{B:Filter (ℕ×ℕ)}{L:Layout F} {D:Lenses.Mantle F B}{s:Extraction.Sequence}
    (Z:Ledger L)(fx:Flick R.family.path.levels)(W:Services R.family f S)
set_option quotPrecheck false
local notation "C"=> R.family
local notation "ι"=> R.family.path.levels
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "Q"=> wheel R.family
local notation "a"=> R.family.S.a
local notation "T"=>OPE.run
variable {n:ℕ} (d:Fin n→ℕ) (t:ℕ) (b:ℝ→ Fin n→ Cover)(Y m:ℝ→ℕ) {α:ℝ} (h:Lookup R m) (ho:Moored R.family L.level)
abbrev pathTag (R:Run G) (d:Fin n→ℕ)(r:ℝ)(b:Fin n→ Cover) (p:ℕ×ℕ) : Fin n→ Site (R.family.side (wheel R.family r) p.2):= wrap (R.family.side (wheel R.family r) p.2) ∘ b
abbrev readingPrice (L:Layout F) (r:ℝ)(Y m:ℕ)(q v:ℝ) (t:ℕ)(b:Fin n→ Cover)(u:(j:Fin n)→R.family.label (d j))(p:ℕ×ℕ) (z:R.family.label t):Prop:= CollectionR R d t r p.1 p.2 (pathTag R d r b p) (fun i=> atRef L _ r p (u i)) (q*a m^t) v Y m z
variable {r:ℝ}
lemma budgetDress (k l:ℕ) (q v:ℝ) (t:ℕ)(b:Fin n→ Cover)(u:(j:Fin n)→R.family.label (d j)) {M:R.family.label t}(y:ℕ×ℕ→ R.family.label t) {p:Filter (ℕ×ℕ)} [p.NeBot] (hv:p≤L.lens) (hy:Tendsto y p (𝓝 M))(he:∀ᶠ j in p, readingPrice R d L r k l q v t b u j (y j))(hp:R.family.ref t ≤ l) (hz:∀ i,R.family.ref (d i)≤ L.level r) : Dress («C»:=R.family) L.lens S k l (Q r) v (q*R.family.S.a l^t) (OPE.Orbits.names (S:=S) (d:=d) (fun i=> master L _ r (u i))) b t M := by
    let w i : R.family.book.Token:= ⟨d i,locatedRef L _ r (u i)⟩
    let X:ReadLabel C w:= fun i j=> atRef L _ r j (u i)
    refine ⟨hp,p,y,inferInstance,hv,hy,⟨w,funext (fun i=>?_),X,fun i=>tendsRef L hv (v:=fun _=>u i) tendsto_const_nhds (hz i),⟨?_⟩⟩,(he.mono (fun _ hi=>hi.measure))⟩
    · change (⟨_,S.project _ (locatedRef L _ r _)⟩:S.Tag)=(⟨_,S.project _ (S.representative _ _)⟩:S.Tag); rw [S.rep,payRef]; rfl
    filter_upwards [he,(large_mesh f (Q r)).filter_mono (hv.trans L.certified)] with i hi hp
    apply (show Cards.register C (Q r) b (germ X) i.1 i.2=(fun U=>∏ j,R.family.O i.1 i.2 (X j i) (attachV R (Q r) (p:=i.2) (pathTag R d r b i) i.1 j) U) from ?_).symm ▸ hi.load
    funext U; rw [germ_here]; refine Finset.prod_congr rfl fun j _=>?_
    unfold Cells.location attachV; rw [dif_pos hp,vect C _ i.2 i.1 _ hp]; rfl
lemma scenes (k l:ℕ)(hp:R.family.ref t ≤ l)(u:(j:Fin n)→R.family.label (d j)) (q v:ℝ) (he:∀ᶠ i in L.lens,∃ z, readingPrice R d L r k l q v t (b r) u i z): ∃ (y:ℕ×ℕ→R.family.label t) (M:R.family.label t) (p:Filter (ℕ×ℕ)), p.NeBot ∧ p≤L.lens∧ Tendsto y p (𝓝 M)∧ ∀ᶠ j in p, readingPrice R d L r k l q v t (b r) u j (y j):=by
    letI:= L.notbot
    let y i:= if hy:∃ z, readingPrice R d L r k l q v t (b r) u i z then hy.choose else 0
    have he:∀ᶠ i in L.lens, readingPrice R d L r k l q v t (b r) u i (y i):=he.mono fun i h=>by unfold y; rw [dif_pos h]; exact h.choose_spec
    obtain ⟨A,hA,hκ⟩:=quota_stop R.family R.makes hp
    obtain ⟨φ,hφ,hY,Z,hZ⟩:= finite_extract (𝓛:=L.lens) y (A*(q*R.family.S.a l^t)) (by filter_upwards [he,(large_mesh f l).filter_mono L.certified] with i hi hh using (hκ i.1 i.2 _ hh).trans (mul_le_mul_of_nonneg_left hi.measure hA))
    exact ⟨y,Z,φ,hY,hφ,hZ,he.filter_mono hφ⟩
include W Z fx in
lemma buys_words (hY:Height R.family.S home T Y α)(hh:α<1) {f₀:ℕ} {u:ℝ→(j:Fin n)→R.family.label (d j)} (j:Fin n) (he:∃ u r D,OPE.Log.LogPackage R.family u r D)(h:Lookup R m) (ho:Moored R.family L.level)(ha:∀ᶠ r in home,∀ i:Fin n,Paid L r (u r) i≤ H (Q r)^f₀) : ∃ q v:ℝ→ℝ,ValueStamp home T q ∧ RateLE home T v (-((t+1/16:ℝ)*(1-α)))∧ ∀ b:ℝ→ Fin n → Cover,∀ x:Points n,x∈generic n → Tendsto (fun r=>tag (role R.family r) (b r)) home (𝓝 x)→∀ᶠ r in home,∃ (y:ℕ×ℕ→R.family.label t) (X:R.family.label t) (p:Filter (ℕ×ℕ)), p.NeBot ∧ p≤L.lens∧ Tendsto y p (𝓝 X)∧ ∀ᶠ j in p, readingPrice R d L r (Y r) (m r) (q r) (v r) t (b r) (u r) j (y j):=by
    obtain ⟨f',ℓ,D',h'⟩:=he
    obtain ⟨q,v,hq,hV,hκ⟩:= assuresG R Z fx W j d t f₀ Y m h' ho h hY hh
    refine ⟨q,v,hq,hV,fun b x hx hv=>?_⟩; filter_upwards [hκ x b hx hv,h.spine.grows.eventually_ge_atTop (R.family.ref t),ha] with r he hr ha using scenes R d t b (Y r) (m r) hr (u r) (q r) (v r) (he.mono fun i hi=> hi (u r) ha)
include W Z fx
lemma yields_reads (p:ℝ→ℝ)(M:ℝ→R.family.label t)(q:ℝ→ℝ) (v:ℝ→ (j:Fin n)→ R.family.label (d j)){α:ℝ}(h:Height R.family.S home T Y α)(ha:0<α)(hb:α<1){w:ℕ}(ht:∀ᶠ r in home,∀ i:Fin n,Paid L r (v r) i≤ H (Q r)^w) {x:Points n}(hr:Tendsto (fun r=>tag (role R.family r) (b r)) home (𝓝 x))(hx:x∈generic n) (hL:Lookup R m) (hh:RateLE home T p (-((t+1/16:ℝ)*(1-α)))) (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (hX:∀ᶠ r in home,∃ (y:ℕ×ℕ→R.family.label t) (p':Filter (ℕ×ℕ)), p'.NeBot ∧ p'≤L.lens∧ Tendsto y p' (𝓝 (M r))∧ ∀ᶠ j in p', readingPrice R d L r (Y r) (m r) (q r) (p r) t (b r) (v r) j (y j)): RateLE home T (fun r=> P.packet t (R.family.S.gridPoint (wheel C r) ∘ b r) (d:=d) (fun i=>master L _ r (v r i)) 0 - S.project t (M r)) (-((t+1/16:ℝ)*(1-α))):=by
    have hV: GradePrice P d (fun r i=>master L _ r (v r i)) 0:=fun i j=>by
        let z(r):= L.shift (d i) r (v r i); apply (engineeringUpper P L Z.reach W (d i) j z ?_).mono
        · simp
        have hX:=runMount R Z fx; exact RateLE.of_norm_le (f:=fun r=> H (Q r)^w) (((hX.power w).pays ageLarge).mono (by norm_num)) (ht.mono (fun r hr=> (RG12.norm_le_mass ..).trans (hr i)))
    have hz : ∀ᶠ i in home,Dress («C»:=R.family) L.lens S (Y i) (m i) (Q i) (p i) (q i*a (m i)^t) (OPE.Orbits.names (S:=S) (d:=d) (fun j=>master L _ i (v i j))) (b i) t (M i):=by
       filter_upwards [hX,(eventually_all.mpr fun j=>Z.reach.growing.eventually_ge_atTop (R.family.ref (d j))), hL.spine.grows.eventually_ge_atTop (R.family.ref t)] with r hr he hP; obtain ⟨y,φ,hY,hφ,hQ,hU⟩:=hr; exact budgetDress R d (Y r) (m r) (q r) (p r) t (b r) (v r) y hφ hQ hU hP he
    apply (fines F W P Y m Q ha hb h (goingWheel R Z fx) L.certified _ b M hz hh ?_ hV ?_).mono ?_
    · filter_upwards [launches Z fx le_rfl hr hx] with i hi using hi.1
    · obtain ⟨a',ha',hA⟩:= Metric.nhds_basis_closedBall.mem_iff.mp ((conf_open n).mem_nhds (generic_conf n hx)) -- ha'
      obtain ⟨X,η,hX,hη,hκ⟩:= roomCosts (isCompact_closedBall x a') hA; refine ⟨X,η,hX,hη,?_⟩; filter_upwards [hr.eventually (Metric.closedBall_mem_nhds _ ha'),positiveLength] with i hi hv
      rw [show R.family.S.gridPoint (wheel C i) ∘ b i= posed i (tag (role C i) (b i)) from funext fun j=>congr_arg (fun x:Points n=> x j) (scaledRole hv (b i)).symm]; exact hκ _ hv _ hi
    exact max_le (by have h:0 ≤ (t:ℝ):= Nat.cast_nonneg _; nlinarith only [h,ha]) le_rfl
end YM.RG17
