import YM.QuadraticLocal.Aperture.Toggle
/-!
 # Valence of the term with a given inertia

 Because the (auxiliary!) experiment uses `h` powers of the coupling to pay a marker, ordinary
 coefficient azimuth at `k` can at most involve `k/h` occurrences. PRESERVE this in exponent,
 vacuum ratio numerator/denominator and projection to regular connected deposit. Real λ alternating
 differences then pointwise exactly recover the coefficient *of every marker* (in one test query!)
 up to the stipulated order before any repeated markers contributing. Go much higher when setting
 up to also buy the uniformly accurate derivative interpolation.

 Uses only Rank φ horizon bound if possible; doesn't appeal to high-norm of older Fk equations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Aperture.Drawer
open Function Filter MeasureTheory Finset Lattice
open Topology AllOrder AllOrder.Fire AllOrder.Laplace
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open Marker Multi Sunrise
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge}{X V:Type} [Fintype V] {Y:Type}{k m n:ℕ}
variable (V) (C:Drawer Y)
def crown (k m:ℕ):= k/m
local notation "P"=> (V→ℝ) × Y
abbrev Inn (h: ℕ) (L:Book (Knife V × Y)): Prop := ∀ i:ℕ,School C (i/h) (L i)
namespace Inn
variable {V C}{F G:Book ((V→ℝ) × Y)}
lemma sail (h:Inn V C n F)(hG:Inn V C n G): Inn V C n (alters F G):= by
 intro u; rw [show alters F G u = ∑ i∈range (u+1), F i * G (u-i) from ?_]; swap; · exact funext (fun i=> (plus_real F G i u).trans (by rw [Finset.sum_apply]; rfl)); -- plus_real form check (ih.conv(gΘ)).
 apply School.pivot; intro i hi; have he:= (h i).product (hG (u-i)); apply he.up; rw (occs:=.pos [2]) [← Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]; exact Nat.add_div_le_add_div _ _ _ -- names likely
lemma horizon (h:Inn V C n F)(s:ℕ): Inn V C n (energy F s):= by
 induction s with
 | zero=> intro i; rw [level]; exact School.stable V C _ (just (1:ℝ) i)
 | succ i ih=> rw [powered]; exact ih.sail h
lemma vita (h:Inn V C n F)(f:Tape)(k:ℕ) : Inn V C n (arrow f F k):= by
 intro i; unfold arrow; rw [Finset.sum_apply]; exact School.pivot _ (fun p _=>(h.horizon p i).scale _)
section thanks
-- `Wallet.Expo` `[Norm...]`. Might generalize X to auxiliary PUnit rank query or Y chart. Add tokens when Adj.Book.Phys better.
variable [NormedAddCommGroup Y][NormedSpace ℝ Y]
lemma tall (h:Inn V C n F)(he:F 0=0): Inn V C n (EXP F):= by intro i; rw [Expo he (le_refl i)]; apply h.vita
lemma loose (h:Inn V C n F)(he:F 0=1): Inn V C n (LOG F):= by
 intro i; rw [Lords he (le_refl i)]; refine vita ?_ _ _ _
 exact fun i=> (h i).sub (School.stable _ _ _ (just (1:ℝ) i))
end thanks
lemma take_valley (h:Inn V C n F)(T:X→(Y→ℝ)→ℝ) (C':Drawer X)(he:∀ u:Y→ℝ,C u → C'.Screen (fun x=>T x u))(hs:∀ u v:Y→ℝ,C u→C v→∀ x,T x (u+v)=T x u+T x v)(hf:∀ u:Y→ℝ,C u→∀ (p:ℝ) x,T x (p•u)=p*T x u) : Inn V C' n (fun i x=> T x.2 (fun y=> F i (x.1,y))) := fun i=> School.cost T _ he hs hf (h i)
end Inn
open Toggle Focus Response School
variable {C} (C':Drawer X)
-- without proof powers.Transpose. `hemat` for arbitrary k order when ambient vacuum aperture. true rank coefficient agreement LIVE beyond marks.
variable {T: X→ℝ}(x:X) {u : (V→ℝ) × X→ℝ} {v:Book ((V→ℝ) × X)}
variable [DecidableEq V]
lemma smallP (L:Multiset V)(h:L.card < Fintype.card V): Toggle.alt (fun u: V→ℝ=> view u L)=0:=by
 by_cases ht: ∃ i:V,i∉L
 · obtain ⟨i,h⟩:=ht; exact opposite i L h
 push Not at ht; rw [sold L h.le ht] at h; exact (Nat.lt_irrefl _ h).elim
lemma seen_s (h:Drawer.School C' k u)(hp:k < Fintype.card V): Toggle.alt (fun z:V→ℝ=> u (z,x))=0:=by
 induction h with
 | one L h f hf=>
    let a(p:V→ℝ):=view p L; rw [show (fun u:V→ℝ=> shape L f (u,x))= (f x) • a from funext fun i=> mul_comm _ _,Toggle.alt_times,show Toggle.alt a=0 from smallP V _ (h.trans_lt hp),mul_zero]
 | @graft F' g h hv a b=>
    let f z:= F' (z,x); let g' z:= g (z,x); change alt (f+g')=0; rw [alt_plus,a,b, add_zero]
lemma tier_l (h:Inn V C' m v)(hm:0< m) (hp:k< Fintype.card V*m): Toggle.alt (fun z:V→ℝ=> v k (z,x))=0:= seen_s V C' x (h k) ((Nat.div_lt_iff_lt_mul hm).2 hp)
end YM.QuadraticLocal.Aperture.Drawer
