import YM.WilsonCoeffUV.Kinetic.Extraction
import YM.WilsonCoeffUV.Ward.AxisColor
/-!
# Log residual factorial interface through the first loop
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue.Cameo
open Matrix Function PowerSeries
open scoped BigOperators ContDiff
variable {U V I:Type*}{p q: Ink I}{n:ℕ}

-- trunk interface
structure Mist (u:U→I)(p:Ink I): Prop where
   first i: Dark 2 (brush (u i) p)
   second i j: Dark 3 (brush (u i) (brush (u j) p))
lemma Mist.add {u:U→ I}(x:Mist u p)(y:Mist u q): Mist u (p+q) := ⟨fun i=> by rw [map_add]; exact (x.first _).lamp (y.first i),fun i j=> by rw [map_add,map_add]; exact (x.second _ _).lamp (y.second i j)⟩
lemma Mist.neg {u:U→ I}(x:Mist u p): Mist u (-p):= ⟨fun i=>by rw [map_neg]; exact (x.first i).sham,fun i j=> by rw [map_neg,map_neg]; exact (x.second i j).sham⟩
lemma Mist.raise {u:U→ I}(h:constantCoeff p=0)(g:Mist u p): Mist u (raiseE p):=by
   have hp i: brush (u i) (raiseE p)= raiseE p * brush (u i) p:=raise_diff h _
   have hx i : Dark 2 (brush (u i) (raiseE p)):=by rw [hp]; exact (g.first i).rune _
   refine ⟨hx,fun i j=>?_⟩; rw [hp,Derivation.leibniz]; exact ((g.second i j).rune _).lamp (((g.first j).eclipse (hx i)).faint (by omega))
lemma Mist.low {u:U→ I}(h:constantCoeff p=1)(g:Mist u p): Mist u (logOf p):=by
   let q:=logOf p; have hh: constantCoeff q=0:= constantCoeff_logOf h
   have he p' : brush p' p=p*brush p' q:= by have hx: brush p' (raiseE q)=raiseE q*brush p' q:=raise_diff hh _; rwa [show raiseE q=p from raising_log h] at hx
   have hx:IsUnit p:=PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [h]; exact isUnit_one)
   have hz i : Dark 2 (brush (u i) q):=by
       apply Dark.times hx; rw [← he]; exact g.first i
   refine ⟨hz,fun i j=>?_⟩; change Dark 3 (brush (u i) (brush (u j) q)); apply Dark.times hx; have hp:= congr_arg (brush (u i)) (he (u j));
   rw [Derivation.leibniz] at hp; change brush (u i) (brush (u j) p)=p* brush (u i) (brush (u j) q)+brush (u j) q * brush (u i) p at hp; rw [eq_sub_of_add_eq hp.symm, sub_eq_add_neg]
   exact (g.second i j).lamp ((((hz j).eclipse (g.first i)).faint (by omega)).sham)

lemma W_dark [Fintype U][Fintype V]{P:Ink (U⊕V)}(X:Matrix U U ℝ)(h:Dark n P): Dark n (Wick V X P):=by
   intro i he; unfold Wick projectZero; rw [coeff_map, overlay_apply,h.off he,map_zero,map_zero,map_zero]
lemma Mist.wick [Fintype U][Fintype V]{P:Ink (U⊕V)} (H:Matrix U U ℝ)(g:Mist (U:=V) Sum.inr P): Mist id (Wick V H P):= ⟨fun i=>by change Dark _ (brush i _); rw [← W_D]; exact W_dark H (g.first i),fun i j=>by change Dark _ (brush i (brush j _)); rw [← W_D, ← W_D]; exact W_dark H (g.second i j)⟩
lemma glaze_log [Fintype U][Fintype V]{f:Ink (U⊕V)} (H:Matrix U U ℝ) (h:constantCoeff f=0): constantCoeff (Wick V H (raiseE f))=1:=by rw [Wick,projectZero,←coeff_zero_eq_constantCoeff_apply,coeff_map,overlay_apply,coeff_zero_eq_constantCoeff_apply,raise_one h,glaze_one,map_one]
theorem faux [Fintype U][Fintype V]{P:Ink (U⊕V)}(K:Matrix U U ℝ)(h:constantCoeff P=0)(p: BrushGrade P): Mist id (logOf (Wick V K (raiseE P))) := (((Mist.raise h ⟨p.1,p.2⟩).wick K).low (glaze_log K h))

variable {Z:Type}[Fintype Z]
lemma toll_total (p:Pal ℝ Z)(t:ℕ)(r)(h:shellK r p): coeff t (flash p)= ∑ i∈Finset.range (r+t+1),paint i (p t i):=by rw [flash,coeff_mk]; exact visible fun i hi=> h t i hi
lemma tally_sub (p q:Pal ℝ Z){k e}(u:shellK k p)(w:shellK e q): flash (p-q)=flash p-flash q:= flash_sub (finite_shell u) (finite_shell w)
-- invisible ranks
omit [Fintype Z] in
lemma fallen (p:Gen ℝ Z)(n)(h:∀ i,sever i p n=0): p (n+1)=0:=by
    funext x; have he := congr_fun (h (x 0)) (Fin.tail x)
    simp only [sever, Pi.smul_apply, nsmul_eq_mul, prune,Fin.cons_self_tail,Pi.zero_apply] at he
    exact (mul_eq_zero.mp he).resolve_left (by positivity)
lemma blind (p:Gen ℝ Z) (v:FiniteGen p)(g:Pure p)(w:∀ i,MvPolynomial.pderiv i (totalR p)=0) (n:ℕ)(h:1≤ n): p n=0:=by
    -- derivative annihilate via peel; map total then total equality all positive smooth.
    cases n with
    | zero=> omega
    | succ n=> apply fallen; intro i; rw [show sever i p=0 from ?_]; rfl
               apply Power.gen_inj (finite_sever i v) ⟨0,fun _ _=>rfl⟩ (pure_sever i g) Pure.zero
               rw [visible_sever v g,w]; simp [totalR]
lemma veiled (P:Pal ℝ Z){l}(h:Mist id (flash P))(v:shellK l P)(p:∀ i,Pure (P i)) (n k)(ht:n≤1)(hp:1≤ k): P n k=0:= blind (P n) (finite_shell v n) (p n) (fun i=>by have he:= (h.first i).off (i:=n) (by omega); rw [brush,blot_apply,flash,coeff_mk] at he; exact he) k hp
lemma opaqueGain (P:Pal ℝ Z){l}(h:Mist id (flash P))(v:shellK l P)(p:∀ i,Pure (P i)) (n k)(ht:n≤2)(hp:2≤ k): P n k=0:=by
   cases k with
   | zero=> omega
   | succ k=> apply fallen; intro i;
              refine blind _ (finite_sever i (finite_shell v n)) (pure_sever i (p n)) (fun j=>?_) k (by omega)
              have he:= (h.second j i).off (i:=n) (by omega); simp only [brush,blot_apply,flash,coeff_mk] at he; rw [visible_sever (finite_shell v n)]; exacts [he,p n]
end YM.WilsonCoeffUV.Blue.Cameo
