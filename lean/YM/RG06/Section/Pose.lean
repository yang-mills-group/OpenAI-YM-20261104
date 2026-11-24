import YM.RG06.Section.Direct
/-!
# Pose recipe independent expansion

No need to choose a unique representation of lattice stencil; equality of
bare germs uses smooth jet at zero and no continuum limits. Constant
term on the color curl symbol and lens identification in following module.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Section
open RG06 Weak Lattice Pert Function RG Source Drops Labels Bid
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{d m : ℕ}{F : Labels.Frame G d}
local notation "V"=> RG.Slot × G.ColorIndex
variable {s : Finset Cover}

def issue (B : Fin m → RG.Slot)(p : Pose G m)(a:Links ℤ G.Color)(l : ℕ): PowerSeries ℂ:= Weak.divideRecipe l PowerSeries.C PowerSeries.X (fun i:Fin m×G.ColorIndex=>curvedSlot a (B i.1,i.2)) p

lemma pose_exact {D : SectionData F}{i:F.Index}{B : Fin m→ RG.Slot}{p : Pose G m}(a:Links ℤ G.Color)
    (hp:D.evaluate (Pi.single i 1)=lumin p ∘ mapped B) (hq:lows p (F.grades i).2): Weak.DeSlot (F.grades i).2 (fun t=> D.evaluate (Pi.single i 1) (ray a t)) (issue B p a (F.grades i).2):=by
  simp_rw [hp]; exact DeSlot.eval _ p (fun k=> divided a (B k.1,k.2)) hq

lemma sameCylinder {D : SectionData F}{i:F.Index}{B : Fin m→ RG.Slot}{p : Pose G m}(a:Links ℤ G.Color)
    (hp:D.evaluate (Pi.single i 1)=lumin p ∘ mapped B) (hq:lows p (F.grades i).2):
    direct D (tile a) (Pi.single i 1)=issue B p a (F.grades i).2 * PowerSeries.X^(F.grades i).2:=by
  have ht:=direct_eq D (ray_tiled a) (Pi.single i 1)
  have hf:=pose_exact a hp hq
  ext k; exact (Writes.coeff ht k).symm.trans (Writes.coeff hf k)

/-- Same result by extracting from the literal mat/index symbols (so even
without accessing the chosen slots we have the normalized symbols). -/
def start (D : SectionData F)(a:Links ℤ G.Color)(i : F.Index): PowerSeries ℂ:=PowerSeries.mk (fun n=>PowerSeries.coeff (n+(F.grades i).2) (direct D (tile a) (Pi.single i 1)))

lemma sameStart {D : SectionData F}{i:F.Index}{B : Fin m→ RG.Slot}{p : Pose G m}(a:Links ℤ G.Color)
    (hp:D.evaluate (Pi.single i 1)=lumin p ∘ mapped B) (hq:lows p (F.grades i).2): start D a i=issue B p a (F.grades i).2:=by
  ext k; rw [start,PowerSeries.coeff_mk,sameCylinder a hp hq,PowerSeries.coeff_mul_X_pow]

theorem normalized_start (D : SectionData F)(P : pop D)(i:F.Index)(a:Links ℤ G.Color): Weak.DeSlot (F.grades i).2 (fun t=> D.evaluate (Pi.single i 1) (ray a t)) (start D a i):=by
  obtain ⟨m,B,_,p,hp,hq⟩:=P i; rw [sameStart a hp hq]; exact pose_exact a hp hq

theorem starts_unit {H:Hol G}(D:SectionData F)(h:D.Sound H)(P : pop D)(a:Links ℤ G.Color): start D a 0=1 :=by
  have hv:=normalized_start D P 0 a
  unfold DeSlot at hv
  rw [F.zero_degree] at hv; simp only [pow_zero,mul_one] at hv
  change WritesPS (fun t=>D.evaluate F.e0 (ray a t)) _ at hv; rw [h.unit] at hv
  have hz:=WritesPS.constant (1:ℂ); rw [map_one] at hz; ext i; exact (Writes.coeff hv i).symm.trans (Writes.coeff hz i)

lemma common_torus {D : SectionData F}{i:F.Index}{B : Fin m→RG.Slot}{p : Pose G m}{n : Side} (a:Links (Per n) G.Color)(o:Site n)
    (hp:D.evaluate (Pi.single i 1)=lumin p ∘ mapped B)(hq:lows p (F.grades i).2):
    Weak.DeSlot (F.grades i).2 (fun t=>D.places (Pi.single i 1) o (ray a t)) (issue B p (placeColor a o) (F.grades i).2):= pose_exact (placeColor a o) hp hq

theorem torus_start {D : SectionData F}(P:pop D)(i:F.Index){n : Side}(a:Links (Per n) G.Color)(o:Site n):
    Weak.DeSlot (F.grades i).2 (fun t=>D.places (Pi.single i 1) o (ray a t)) (start D (placeColor a o) i):=normalized_start D P i (placeColor a o)

-- constant term selects the pure component of the slot formula.
open MvPolynomial (coeff IsWeightedHomogeneous weightedHomogeneousComponent)

def heading (B : Fin m→ RG.Slot)(p:Pose G m)(l:ℕ): MvPolynomial V ℂ := MvPolynomial.rename (fun i=>(B i.1,i.2)) (weightedHomogeneousComponent (fun _=>1) l p)

theorem originValues (B : Fin m→ RG.Slot)(p:Pose G m)(a:Links ℤ G.Color)(l:ℕ)(h:lows p l):
    PowerSeries.constantCoeff (issue B p a l)= MvPolynomial.aeval (linearSlot a) (heading B p l):=by
  unfold heading
  rw [MvPolynomial.aeval_rename, MvPolynomial.aeval_eq_eval₂Hom,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_eq]
  unfold issue Weak.divideRecipe
  rw [_root_.map_sum,MvPolynomial.support_weightedHomogeneousComponent, Finset.sum_filter]; apply Finset.sum_congr rfl; intro b hb
  simp only [map_mul,map_pow,PowerSeries.constantCoeff_C,PowerSeries.constantCoeff_X,
    Weak.monoval, map_prod,map_pow,linear_slot,MvPolynomial.coeff_weightedHomogeneousComponent,Finsupp.weight_apply, comp_apply,Algebra.algebraMap_self,RingHom.id_apply]
  have he:=h b hb; by_cases hx : count b=l
  · unfold Weak.count at *; simp [hx]
  have hy : count b-l≠0:= Nat.ne_of_gt (Nat.sub_pos_of_lt (lt_of_le_of_ne he (Ne.symm hx)))
  unfold Weak.count at *; simp [hx,hy]
end YM.RG06.Section
