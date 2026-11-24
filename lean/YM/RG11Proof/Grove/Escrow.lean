import YM.RG11Proof.Grove.Carpet
import YM.RG11Proof.Scale.Vanish

/-! # Powerlog reproduction is transported and identifies the same truncated OPE

At fixed subtraction length one, relative profiles/points held; measured from
FULL moments incl unit, not asserting identification of connected OPE in a
different convention. Enter only smooth separated profiles or prove an
adapter. Here `Probe` includes every announced insert word (labels varied at
fixed exterior geometry), so need correlation match on full product AND after
output localization. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Grove
open PowerSeries YM.RG11.Jets YM.RG11.Scale
open scoped BigOperators Classical Topology
variable {I O E Γ:Type*}
local notation "ps"=>PowerSeries ℂ

-- E includes varying labels at fixed exterior configurations (maybe multiple); I = whole
-- input already (tuple or graph), captures with no coincident singularities.
abbrev Cabinet (I O:Type*) := ℝ → Rect I O (PowerSeries ℂ)

variable [Fintype O]
def oddity (s:ℝ)(F:Rect I E ps)(G:Rect O E ps)(C:Cabinet I O):Rect I E ps:= F-C s * G

def EventRate (q:ℕ)(H:ℕ)(e:ℝ)(d:I→ℕ)(F:ℝ→Rect I E ps)(G:Rect O E ps)(C:Cabinet I O):Prop:=
   Affords (fun i (_ : E)=> individual ((d i:ℝ)-H-e)) q (fun s=>oddity s (F s) G C)

/-- Reproduction using same tags, in a supplied geometry uniform domain.
 *Input cost* L already incorporates any powers of Λ or reciprocals of
 separation. No extra incurred in this fixed-horizon implication; coefficient
 order N fixed and exterior frames independent of ratio. Includes derivative
 questions if N-demand paying those coefficients through them. -/
def Cones (q:ℕ)(H:ℕ)(e:ℝ)(d:I→ℕ)(Ω:ℝ→Set Γ)(L:ℝ→Γ→ℝ)
   (F:ℝ→Γ→Rect I E ps)(G:ℝ→Γ→Rect O E ps)(C:Γ→Cabinet I O):Prop:=Covers Ω L (fun i (_:E)=> (d i:ℝ)-H-e) q (fun s o=>oddity s (F s o) (G s o) (C o))

section
variable [Fintype I][Fintype E](p:ps)(U:Square I ps)(V:Square O ps)(Z:Square E ps)

def reassign (C : Cabinet I O):Cabinet I O:=fun s=>rug p U (C s) V -- V here already inverse

-- commute and pay
 theorem shifts {N}(ha:Anchored p){W:Square O ps}(hWV:W*V=1)(s:ℝ)
    {F A:Rect I E ps}{G B:Rect O E ps}(hF: MatThrough N A (rug p U F Z))(hG: MatThrough N B (rug p V G Z))(C:Cabinet I O):
    MatThrough N (oddity s A B (reassign p U W C)) (rug p U (oddity s F G C) Z):=by
   have he:MatThrough N (oddity s A B (reassign p U W C)) (oddity s (rug p U F Z) (rug p V G Z) (reassign p U W C)):=fun i j=> (hF i j).sub (((MatThrough.refl _ (n:=N)).mul hG) i j)
   convert! he using 1
   unfold oddity rug reassign
   let f:ps→ₐ[ℂ]ps:=substAlgHom (R:=ℂ) ha.permits
   have ht(t:ps):PowerSeries.subst p t=f t:= congrFun (coe_substAlgHom ha.permits) t |>.symm
   have hu (t y:Rect I E ps): subs p (t-y)=subs p t - subs p y:=Matrix.ext fun i j=>by rw [subs_apply,Matrix.sub_apply,Matrix.sub_apply,subs_apply,subs_apply,ht,ht,ht,map_sub]
   rw [hu,subs_mul ha,Matrix.mul_sub,Matrix.sub_mul]
   congr 1
   unfold rug
   simp only [Matrix.mul_assoc];
   rw [←Matrix.mul_assoc (l:=_) W V, hWV, Matrix.one_mul]

 theorem translate {i:I→ℕ}(ha:graded i U){W:Square O ps}(hWV:W*V=1){N}(h:Anchored p){F A:ℝ→Rect I E ps}{G B:Rect O E ps}
    (ht:∀ s,MatThrough N (A s) (rug p U (F s) Z))(hT: MatThrough N B (rug p V G Z)){C:Cabinet I O}{d:ℕ}{e:ℝ}(hx:EventRate N d e i F G C):
   EventRate N d e i A B (reassign p U W C):=by
     apply Affords.replace _ (fun s=>shifts _ _ _ _ h hWV _ (ht s) hT _)
     exact ((hx.roof h).left (fun x g j he=> by rw [show i x=i g from not_not.mp fun hv=>he (@ha x g hv)])).right (fun x g j _=> le_rfl)

 theorem translate_all {i:I→ℕ}(ha:graded i U){W:Square O ps}(hWV:W*V=1){N}(h:Anchored p){F A:ℝ→Γ→Rect I E ps}{G B:ℝ→Γ→Rect O E ps}
    (ht:∀ s x,MatThrough N (A s x) (rug p U (F s x) Z))(hT: ∀ s x,MatThrough N (B s x) (rug p V (G s x) Z)){C:Γ→ Cabinet I O}{d:ℕ}{e:ℝ}{Ω:ℝ→Set Γ}{L:ℝ→Γ→ℝ}(hL:Actual Ω L)
    (hx:Cones N d e i Ω L F G C):
    Cones N d e i Ω L A B (fun x=>reassign p U W (C x)):=by
   unfold Cones Covers; intro u j n hn
   have he(s:ℝ)(x:Γ):=shifts _ _ _ _ h hWV s (ht s x) (hT s x) (C x) u j n hn
   simp_rw [he]
   have hb: graded (fun _:E=>0) Z:=fun hh=>False.elim (hh rfl)
   exact graded_envelope (w:=fun _:E=>0) (v:=i) (e:=fun a _=> (a:ℝ)-d-e) hL h (fun ht=>ha ht) (fun he=>hb he) hx _ _ _ hn

-- version with matching on eventual Ω only instead of ∀ s (e.g. kernel reads point evaluations for s in legal separation windows).
 theorem translate_domain {i:I→ℕ}(ha:graded i U){W:Square O ps}(hWV:W*V=1){N}(h:Anchored p){F A:ℝ→Γ→Rect I E ps}{G B:ℝ→Γ→Rect O E ps}
    {Ω:ℝ→Set Γ}(ht: ∀ᶠ s:ℝ in Filter.atTop,∀ x∈Ω s,MatThrough N (A s x) (rug p U (F s x) Z) ∧ MatThrough N (B s x) (rug p V (G s x) Z)){C:Γ→Cabinet I O}{d:ℕ}{e:ℝ}{L:ℝ→Γ→ℝ}(hL:Actual Ω L)(hx:Cones N d e i Ω L F G C):
    Cones N d e i Ω L A B (fun x=>reassign p U W (C x)):=by
    have hl:=translate_all p U V Z (Γ:=Γ) (A:=fun s l=>rug p U (F s l) Z) (B:=fun s l=>rug p V (G s l) Z) (N:=N) (fun e=>ha e) hWV h (fun s x=>MatThrough.refl _) (fun s x=>MatThrough.refl _) hL hx
    intro z j n hn
    obtain ⟨Q,r,hQ,hX⟩:= hl z j n hn
    refine ⟨Q,r,hQ,?_⟩
    filter_upwards [hX,ht] with s hs hy x hh
    apply le_trans _ (hs x hh)
    obtain ⟨he,hu⟩:=hy x hh
    exact (congrArg norm ((he z j).sub (((MatThrough.refl _).mul hu) z j) n hn)).le
end

section identifies
variable {D:Square O ℂ}(W:Square O ℂ)

-- `G` fixed test determines through H already at uniform u-independent
-- price: I whole matrix rows tuples; if reconstruction from two exteriors
-- yields full rank O SAME at all u enough. Use grading PL assumption on C
-- and C', not on free G which may pair across grades at this geometry.
 theorem free_unique {N H}{d:I→ℕ}{w:O→ℕ}(hw:∀ i,w i ≤ H){A:ℝ→Rect I O ps}{G:Square O ps}(ht: G.map constantCoeff * W=1)
    {e:ℝ}(hp:0<e){C T:Cabinet I O}(h:EventRate N H e d A G C)(he:EventRate N H e d A G T)
    (hq: Affords (fun i j=>season ((d i:ℝ)-w j)) N C)(hm: Affords (fun i j=>season ((d i:ℝ)-w j)) N T):
    ∀ s,MatThrough N (C s) (T s):=by
    intro s i j k hk
    induction k using Nat.strong_induction_on generalizing s i j with
    | h k ih=>
      let U s:= C s - T s
      let D(s:ℝ):=piece k (U s)
      let V(r:I):=(d r:ℝ)-H-e
      let M(r:I):= individual (V r)
      have hu (r t):(fun s=>coeff k ((U s * G) r t))∈ M r:=by
         simp_rw [U,Matrix.sub_mul,Matrix.sub_apply,map_sub]
         have hb := (M r).sub_mem (he r t k hk) (h r t k hk)
         convert! hb using 1; ext u; dsimp [oddity,M]; rw [map_sub,map_sub]; ring
      let Z:=G.map constantCoeff
      have heq(r t):(fun s=>coeff k ((U s*G) r t))=fun s=>(D s * Z) r t:=funext (fun s=>by
           simp only [Matrix.mul_apply,map_sum,piece_apply,D,Z]; apply Finset.sum_congr rfl; intro i _
           refine Scale.hit_coeff k (p:=U s r i) (fun q hq=> by rw [show U s r i=_ from Matrix.sub_apply (C s) (T s) r i,map_sub,ih q hq _ _ _ (hq.le.trans hk),sub_self]) _)
      have hb : (fun s=> D s i j)=(∑ t:O, W t j • (fun s=> (D s * Z) i t)):=by
        funext s; simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
        rw [show (∑ t:O,W t j*(D s * Z) i t)= (D s * Z * W) i j from Finset.sum_congr rfl fun t _=>mul_comm ..,Matrix.mul_assoc,ht,Matrix.mul_one]
      have ho(u:ℝ):(coeff k (C u i j) - coeff k (T u i j))= D u i j:=by simp [D,U]
      apply sub_eq_zero.mp; refine congrFun (a:=s) (wipe (v:=(d i:ℝ)-w j) (f:=fun u=> coeff k (C u i j) - coeff k (T u i j)) (w:=V i) ?_ ?_ ?_)
      · exact Submodule.sub_mem _ (hq i j k hk) (hm i j k hk)
      · simp_rw [ho]; rw [hb]; exact Submodule.sum_mem _ fun t _=> Submodule.smul_mem _ _ (heq i t ▸ hu i t)
      have hx:(w j:ℝ)≤H:=by exact_mod_cast hw j
      unfold V; linarith
end identifies
end YM.RG11.Grove
