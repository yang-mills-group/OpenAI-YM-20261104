import YM.X.Grow.Tele
/-!
# Kernel CT representation. Characterize exact local lattice Taylor lift's free Maxwell-sector gauge-invariant read. Use slip polynomials (canonical, �degree m) and complement separates. Bounds later.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Grow
open MvPolynomial Function Lattice Next.Rank Normal LiftMark Maxwell Maxwell.Free Finset Reed Labels Submodule
open PertExtension LatticePT
open scoped Topology Classical Pointwise
variable {G:Gauge} {V W I:Type*} {u:V→ℕ}{n m k d:ℕ}
local notation "w"=>vapor G
local notation "K"=> Kite (Okay G)
local notation "B"=>Book G
variable {p:B}
def arch (x:Long G):TaylorTower G := fun n=> shelve n (x (n+1))
def stoic (A:TaylorTower G): Long G
 | 0 => 0
 | n+1=> slip (A n)
def rich : WickPol G →ₐ[ℂ] B := MvPolynomial.aeval fun s:Slot G=> colorL (s.1+1) (coordinateLeg s ∘ₗ shelve s.1)
lemma rich_eval (x:Long G)(b): probeL x (rich b)= probe (arch x) b:= by apply DFunLike.congr_fun (f:=(probeL x).comp rich); ext1 i; rw [AlgHom.comp_apply,rich,aeval_X,eyes]; simp [probe];rfl
lemma rich_hom (i:Slot G): IsWeightedHomogeneous w (rich (X i)) (scaleW i):= by rw [rich,MvPolynomial.aeval_X]; have h:= gears (E:=Okay G) (i.1+1) (coordinateLeg i ∘ₗ shelve (G:=G) i.1); exact h
lemma rich_lay (b:Labels.Pol G): layBox b=rich (Maxwell.reduceEq b):= by apply probe_ext;intro x; rw [rich_eval, layBox_test, jet_value];rfl

def spike : (i: Valves G) → WickPol G
 | ⟨0,t⟩=>0
 | ⟨n+1,t⟩=> Maxwell.symbol n (((owns (Okay G) (n+1)).coord t) ∘ₗ slip)
def lessJob:B→ₐ[ℂ] WickPol G:= aeval spike
set_option maxHeartbeats 900000 in
lemma shorter (x:TaylorTower G)(p :B): probe x (lessJob p) = probeL (stoic x) p:= by
     apply DFunLike.congr_fun (f:=(probe x).comp lessJob) (g:=probeL (stoic x)); ext1 i; rw [AlgHom.comp_apply,lessJob,aeval_X,probeL,aeval_X];
     rcases i with ⟨_|n,t⟩; 
     · change probe x (0:WickPol G)=↑((owns (Okay G) 0).coord t (0:Okay G 0)); have he : (owns (Okay G) 0).coord t (0:Okay G 0)=0:= map_zero _; rw [map_zero,he,Complex.ofReal_zero]
     rw [spike,symbol_test]; rfl
lemma less_hom (i: Valves G) : IsWeightedHomogeneous scaleW (lessJob (X i)) (w i):= by
    rw [lessJob,MvPolynomial.aeval_X]; rcases i with ⟨_|n,t⟩; · apply isWeightedHomogeneous_zero
    rw [spike]; exact symbol_hom _ fun i=> i+2
lemma strict (p: WickPol G): lessJob (rich p) = p:= by
     apply Maxwell.equalPol; intro x; rw [shorter,rich_eval]; exact congr_arg (fun z=> probe z p) (funext (fun z=>shelve_slip _))

abbrev physicalJet (G:Gauge)(d:ℕ) : Submodule ℂ (Book G):= LinearMap.range (rich.toLinearMap ∘ₗ (Maxwell.shellSector G d).subtype)
lemma level_ok (l:V→ℕ)(p:poly V) : p∈ restrictSupport ℂ {i|Finsupp.weight l i≤d} ↔level l d p=p:= by
    constructor
    · intro h; ext i; change coeff i (Rise.trim _ _ _)=_; rw [Rise.trim_coeff]; split; rfl; next he=> exact Eq.symm (MvPolynomial.notMem_support_iff.mp (fun h'=>he (mem_restrictSupport_iff ℂ|>.mp h <| h')))
    intro h; apply (mem_restrictSupport_iff ℂ).mpr; intro i hi; change (Finsupp.weight l i) ≤ d; by_contra he; apply mem_support_iff.mp hi; nth_rw 1 [← h]; change coeff i (Rise.trim _ _ _) = _; rw [Rise.trim_coeff,if_neg he]
def Unmixed (d:ℕ)(p:Book G):Prop:= level w d p=p ∧ (∀ u:G.El, pigment u (lessJob p) = lessJob p)
def purely (p:Book G):Prop:= localMap (E:=Okay G) rightCur p=p
lemma slots (p:B) : rich (lessJob p)=localMap (E:=Okay G) (F:=Okay G) (rightCur (G:=G)) p:= by
     apply probe_ext; intro x; rw [rich_eval,shorter,probe_map]; refine congr_arg (probeL · p) (funext ?_); rintro (_|k)<;> rfl
lemma component (p:B) (d:ℕ) : p∈ physicalJet G d↔ Unmixed d p∧ purely p := by
    have he (p: WickPol G) (hp): (level (vapor G) d (rich p)) = rich p := Eq.trans (hom_commute _ (rich_hom (G:=G))) (congr_arg _ hp) -- infer hp
    constructor
    · rintro ⟨⟨b,hb⟩,rfl⟩; let V:= rich b; obtain ⟨hX,hY⟩:= sector.mp hb
      have hi := (level_ok scaleW b).mp (show b∈ restrictSupport ℂ {i| Finsupp.weight scaleW i ≤d} from hX); refine ⟨⟨he b hi,?_⟩,?_⟩; intro u; change pigment u (lessJob (G:=G) V)=lessJob V; rw [show lessJob (G:=G) V=b from strict b]; exact hY u
      change localMap _ V= V; exact (slots V).symm.trans (congr_arg _ (strict b))
    rintro ⟨⟨h,g⟩,p'⟩; have hx : lessJob p ∈ shellSector G d:= by refine sector.mpr ⟨(level_ok scaleW _).mpr ?_,g⟩; rw [hom_commute _ less_hom,h]
    exact ⟨⟨_,hx⟩,(slots p).trans p'⟩
def beam (d:ℕ):Label G d →ₗ[ℂ] (Book G):= layBox.toLinearMap ∘ₗ (localFields G d).subtype
lemma shine (x:Label G d): beam d x = rich (reduceEq x.val):= rich_lay _
lemma beam_range (G:Gauge)(d:ℕ): LinearMap.range (beam (G:=G) d)=physicalJet G d:= by
    apply le_antisymm
    · rintro p ⟨x,rfl⟩; exact ⟨⟨_,⟨x,rfl⟩⟩,(shine x).symm⟩
    · rintro p ⟨⟨x,hx⟩,rfl⟩; obtain ⟨a,rfl⟩:= hx; exact ⟨a,shine a⟩
def flop (d:ℕ) (p:B):= localMap (E:=Okay G) rightCur p -- remove d? decides
lemma flop_jet (p:B)(h:Unmixed d p) : flop d p ∈ physicalJet G d:= by
    apply (component ..).mpr; unfold flop; rw [← slots p]; refine ⟨⟨?_,?_⟩,?_⟩
    · rw [hom_commute _ rich_hom, hom_commute _ less_hom,h.1]
    · intro u; rw [strict]; exact h.2 u
    unfold purely; rw [← slots (rich _),strict]
end YM.PositionX.Grow
