import YM.MS.Menus.Mark
/-!
# Tune table at origin

Leading rank continued curriculum, with memory at larger orders separately. Wake
 quantity dual Q gives exactly price polynomial class. This does not prove Trust
 but allows specialized step when calculating Spheres. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High Ghost Detect
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{B: Deck G}(V : LitBook B)(p:Team) {d n r:ℕ}{v:ℤ}
lemma estimateL {X:Power G}{T:ℝ→ Law G}(x:ℝ)(H:Limit (X.input x).val r)(h:Fits (X.input x) (T x) r (v-1) false): Limit (advance (X.input x)).val r ∧ Fits (advance (X.input x)) (natQ (T x)) r v false:= by
    -- core rank bound
    refine ⟨Limit.add ((lapLimit H).up (by omega)) ((rootLimit (participates G 0) H).up (by omega)),?_⟩; have hh:= early_δ h (X.actual x) H; simpa [Menus.advance] using hh
lemma pens {T:ℝ→ Law G}(h:Ready T)(H:∀ x,T x∈ Lease G v r (-1)): ∃ P: Power G,P.allowance=r ∧ ∀ x,Fits (P.input x) (T x) r v false:= by
   choose F hf hF using fun x=> Ghost.voice (H x); obtain ⟨N,hN⟩:=h
   let L x i: ℂ := ((plate N i).eval x:ℝ); let D: Power G:={
      input x:=∑ i∈Finset.range N, L x i • F i
      polyn:=by convert! (eval_ready N F) using 1
      actual x:= Tune.sum _ (fun i _=> (hf _|>.charge).cash _ (by simp [L]))
      calm x:= Colorless.csum _ (fun i _=> (hf _|>.lit).smul _)
      allowance:=r
      ranks x:= by
          rw [sum_stack]; have he i : Limit (F i).val r:= fun l he=> hf i|>.level l (by rw [mod_int]; omega)
          exact Limit.sum _ (fun i _=> (he _).smul _) }
   refine ⟨D,rfl,fun x=>?_⟩; rw [interpret hN x]; unfold evaluate; rw [show ∑ i∈ Finset.range N, (plate _ i).eval x • T i= ∑ i∈ Finset.range N, L x i • T i from rfl]; exact Fits.sum _ (fun i _=> (hF _).smul _)
namespace Glyph
variable {P S:ℝ→ Law G} {Q:Price B d}
structure Homes (Q:Price B d)(u:ℤ)(r:ℕ): Prop where
    size (c:Glyph B d): Q c≠0→ c.size=u
    grade (c:Glyph B d) : Q c≠0 → c.grade = r
def valAt (Q:Price B d)(x:ℝ) := ∑ c:Glyph B d, (↑((Q c).eval x):ℂ) • c.read
-- support floor; turn on hermitian payments.
lemma hits (h: Homes Q v r)(x:ℝ) : Limit (lighting V p Q x).val r ∧ Fits (lighting V p Q x) (valAt Q x) r v false:= by
    refine ⟨?_,Fits.sum _ (fun i _=>?_)⟩; swap
    · by_cases he: Q i=0; · simp only [he,Polynomial.eval_zero,Complex.ofReal_zero]; rw [zero_smul,zero_smul]; exact Fits.zero _
      rw [← h.size i he, ← h.grade i he]; exact (Glyph.pre_floor V p i x).smul _
    unfold lighting; rw [sum_stack]; refine Limit.sum _ fun c _=>?_ ; by_cases he: Q c=0; rw [he,Polynomial.eval_zero,Complex.ofReal_zero,zero_smul]; exact fun _ _=> rfl; rw [← h.grade c he]; exact Limit.smul _ ((by simpa using pre_cost V p c x 0) : Limit (preamble V p c x 0).val c.grade)
-- offer polynomial class. choose in homogeneous dimension slice only
lemma offered {F:ℝ→ Law G}(hd:0≤v)(hv:v ≤ d)(h:∀ x,F x∈ B.carries v r)(hf: Ready F): ∃ Q:Price B d, Homes Q v r ∧ ∀ x,valAt Q x=F x := by
   lift v to ℕ using hd; by_cases he:r≤v; swap
   · have he : B.carries v r=⊥:= Deck.ceiling B (by omega)
     refine ⟨0,⟨fun i h=> False.elim (h rfl),fun i h=>False.elim (h rfl)⟩,fun x=>?_⟩; specialize h x; rw [he, Submodule.mem_bot] at h; simp [h,valAt]
   let J:=B.BIndex v r; let X:=Module.finBasis ℝ (B.carries v r); let F' x : B.carries v r := ⟨F x,h x⟩; have he x : (∑ j:J, X.repr (F' x) j • B.raw v r j)=F x:= by
       change _= (B.carries v r).subtype (F' x); nth_rw 2 [←X.sum_repr (F' x)]; rw [map_sum]; simp_rw [map_smul]; rfl -- maybe occurrences
   have hp : Ready F':= by
       obtain ⟨a,ha⟩:=hf; rw [show F'=evaluate a F' from funext fun t=> show F' t= evaluate a F' t from Subtype.ext ?_]; swap
       · change F t = (B.carries v r).subtype _; unfold evaluate; rw [map_sum]; simp_rw [map_smul]; exact interpret ha t
       exact eval_ready _ _
   choose Q hQ using fun i:J=> (Ready.linear hp (X.coord i)).scalar
   let s:Fin (d+1):=⟨v,by omega⟩; let a:Fin (s.val+1):=⟨r,by dsimp [s]; omega⟩
   -- explicit support by single glyph images
   let light (j:J): Glyph B d:= ⟨s,a,j⟩; have hl: Injective light:= fun i j h=> eq_of_heq (Sigma.mk.inj ((Sigma.mk.inj h).2 |> eq_of_heq)).2 -- parse
   let W (i:Glyph B d) : Polynomial ℝ:=∑ x:J,if i=light x then Q x else 0
   have hw (i:Glyph B d) (h:W i ≠ 0): ∃ x:J,i=light x:= Classical.byContradiction (fun z=> h (Finset.sum_eq_zero (fun j _=> if_neg (fun h=> z ⟨j,h⟩))))
   refine ⟨W,⟨fun i hx=> by obtain ⟨x,rfl⟩:=hw i hx; rfl,fun i hx=> by obtain ⟨x,rfl⟩:=hw i hx; rfl⟩,fun x=>?_⟩; rw [← he x]; unfold valAt W; simp_rw [Polynomial.eval_finsetSum,Complex.ofReal_sum,Finset.sum_smul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_eq_single (light j)];
   · simp only [if_true]; exact Eq.symm (by rw [show X.repr (F' x) j=(Q j).eval x from congr_fun (hQ j) x]; rfl)
   · intro k _ hk; rw [if_neg hk,Polynomial.eval_zero,Complex.ofReal_zero,zero_smul]
   simp
end Glyph
structure Capacity (A C:Acts B d)(n r:ℕ)(v:ℤ) (H:ℝ→ Law G): Prop where
    past (i:ℕ): i<n→ A i=C i
    size (x:ℝ): Limit ((score V p A x n)-(score V p C x n)).val r
    jet (x:ℝ): Fits ((score V p A x n)-(score V p C x n)) (H x) r v false
-- permits leading reservation: if at order0 and r below highest rank the parameters are special. Later.
lemma room_here (A:Acts B d) {P H:ℝ→ Law G}(h:0≤v)(ht:v≤d)(hp:Ready P)(hq:Ready H) (hc : ∀ i,P i∈B.carries v r)(hd:∀ i,H i∈ Lease G (v-1) r (-1)): ∃ (Q:Price B d) (X:Power G), Glyph.Homes Q v r ∧ X.allowance=r ∧ Capacity V p A (patch A Q X n) n r v (fun i=> P i+natQ (H i)):= by
    obtain ⟨Q,hQ,hF⟩:= Glyph.offered h ht hc hp; obtain ⟨X,hx,hX⟩:= pens hq hd; have he (x:ℝ): Limit (advance (X.input x)).val r∧ Fits (advance (X.input x)) (natQ (H x)) r v false:= estimateL x (hx ▸ X.ranks x) (hX x)
    refine ⟨Q,X,hQ,hx,⟨fun i h=> (patch_bef A Q X h.ne).symm, fun x=>?_, fun x=>?_⟩⟩ <;> rw [repair]; exact (Glyph.hits V p hQ x).1.add (he x).1; rw [← hF x]; exact (Glyph.hits V p hQ x).2.add (he x).2
end YM.MS.Menus
