import YM.AllOrder.Plateau.Penn
/-!
# Connector from the billed polynomial Comparison kernels to small-filament station
- exact identity at all periods, with `off` projector. Winding cost post.
No proof of estimates inherited e error yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext Repeat Lapis Bid Planned.JetPort
open Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush Poll ConnectedActivityE6.Coat
open AbsoluteSums Fare Shellac Work.G05
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G: Gauge} {n : Side} {k j w N : ℕ}
variable {σ C Z D β x₀:ℝ}
local notation "E"=>Positions (Primary n G)
local notation "L"=>Kinetic.Port.exteriorL G n
section know
open Kinetic.Port
variable (P:Patch)(K:KernelChoices){a Λ:ℝ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "M"=> Coarse G
variable {ι:Type} [Nonempty ι]
variable (p:Clip) (O: ChartRatio G)(x:ι→PathData G)(U: ι→ℝ)
variable (Q:Push.Uniform.Before G a C P.J K (N+3)) (hB:P.Branches K G)(hx:∀ i,(x i).Bounds p a C (U i))
    (hO:LocalRatio O)
variable (F:ι→candidates P K G)(h:proofC P K p x Q F)
set_option quotPrecheck false
local notation "V0"=>topiary P K p O x U Q hx hO F h
variable {i:ι} (hn : Ad G P K n) (J: Tube G (dock P K n)) (hU:J.up=x i)(hT:J.high=p)
    (F₀:Forest (dock P K n).ratio) (l₀:(dock P K n).Choices) {ρ : Bid.Dir G n→ AxisChart G F₀} (hp : Critical (S:=dock P K n) F₀ J.high J.up ρ)
variable {θ c y A₁:ℝ}
variable (q:Clip)(V:ι→PathData G)(g:ι→ℝ) (Λ₀:ι→ℝ) (hV:∀i,(V i).Bounds q θ c (Λ₀ i))
    {R:ℕ→ι→Ink.Field (Coarse G)} {S' : Repertoire ι G}
local notation "W"=> (fun (i:ι) k n=>(R k i).table n)
local notation "Θ" => H₀
local notation "Tq"=> ((fun (i:ι)=> Stipend q (V i) (g i)):Theatre G ι)
-- shield cert explicit & post
structure Canopy (Λ:ι→ℝ)(S: ℕ→ι→Ink.Field (Coarse G))(v:Kinetic.Port.Presence P K p O x U Q hx hO F h S) where
 tam : ℕ→ℝ
 sides : ℕ→ι→ℝ
 dust : ℕ→ι→Side→ℝ
 forms (k:ℕ)(hv:k≤N) : Chords P K p O x U Q hx hO F h (tam k) (sides k) (dust k) k (S k) -- binder shadow

structure BillBoard {ι:Type} (Λ:ι→ℝ)(T:Repertoire ι G) (k:ℕ) where
 air : (i:ℕ)→Fin (i+1)→ℝ
 fee : (i:ℕ)→Fin (i+1)→ι→ℝ
 birth (i : ℕ)(hi:i≤k)(t:Fin (i+1)) : 0<air i t ∧ Haiku.Coat.Letter Λ (T i t) (air i t) (fee i t)
lemma BillBoard.ok {Q : Repertoire ι G}{F:Theatre G ι} {k:ℕ}(h:Spliced U F Q (k+1)) : Nonempty (BillBoard U Q k):=by
 choose a ha C he using fun i hi j=>h.age i hi j
 refine ⟨⟨fun i=> if hi:i<k+1 then a i hi else 1,fun i=>if hi:i<k+1 then C i hi else 0,fun i hi j=>?_⟩⟩
 rw [dif_pos (show i<k+1 from Nat.lt_succ_of_le hi),dif_pos (show i<k+1 from Nat.lt_succ_of_le hi)]; exact ⟨ha ..,he ..⟩
local notation "Z₀"=> Presence P K p O x U Q hx hO F h R
-- roles exact
lemma canopy_exists (H : Presence P K p O x U Q hx hO F h R): Nonempty (Canopy P K p O x U Q hx hO F h U R H):= by
 choose a C D hg using fun r hr=> H.fee r hr; refine ⟨⟨fun k=> if h:k≤N then a k h else 1,fun k=>if h:k≤N then C k h else 0,fun k=> if h:k≤N then D k h else 0,fun k hk=>?_⟩⟩; simp only [dif_pos hk]; exact hg k hk
variable (H : Presence P K p O x U Q hx hO F h R)(H₀:Canopy P K p O x U Q hx hO F h U R H)
    (hS:Spliced U ((fun (i:ι) k n=>(R k i).table n)+(fun (i:ι)=> Stipend q (V i) (g i))) S' (N+1)) (B : BillBoard U S' N)
    (hk:k≤N)(hj:k+3 ≤ j)(he:0<β)(B':BareRates.pre G θ c j)
    (hJ:J.down=V i)(hv:J.low=q)(ha:0<y)(hy:y<1)(hu:1≤D)(hD:(Fintype.card (Primary n G):ℝ)≤ D)
variable (X:Positions (Primary n G))(hX:‖X‖≤y)(hG:G.Simple)(hA:PaintSupply G j A₁)
-- budget
abbrev chopWind (i:ι)(j k:ℕ) (b D:ℝ)(n:Side):= ∑ r∈ Finset.range (k+1), (b^r*(tollS D j ((H₀.dust r i n * dearth (H₀.tam r) n * (1+b⁻¹)^(r+2)) * Rail.mantle j (r+2) *2^(r+2))))*2
-- arguments simplify via abbrev.
abbrev chopCut (i:ι)(j k:ℕ) (b D Z y:ℝ) (W' : ℕ) := ∑ l∈ Finset.range (k+1), ∑ r:Fin (l+1), ratioW b l (r.val+2) * shin G (B.air l r) (B.fee l r i) D Z y j (r.val+2) k l W'
-- maybe parameter B implicit h others? check.
def peal (S:Repertoire ι G)(i:ι)(b:ℝ)(W' k:ℕ)(n:Side): Positions (Primary n G)→ℝ:= fun x=> ∑ l∈ Finset.range (k+1),∑ r: Fin (l+1), (ratioW b l (r.val+2)) * speak (crop W' ∘ (S l r i)) n x -- n E shadow
-- syntax
abbrev paid_corner (J : Tube G (dock P K n))(F₀:Forest (dock P K n).ratio) (ρ : Bid.Dir G n→ AxisChart G F₀)(l₀:(dock P K n).Choices) (βα g:ℝ) (k:ℕ) := Local.Pure.script F₀ J O ρ βα l₀ k+βα • staff J.low J.down n+drift J.low J.down g n
local notation "S"=>PhysicalNext.Repeat.Shellac.off
lemma brush_spreeX {E0:Type}[NormedAddCommGroup E0][NormedSpace ℝ E0]{u:E0}{Φ:Type*}(s:Finset Φ){v:Φ→ℝ}{D:ℝ}{f:Φ→ E0→ℝ}(hd:0≤D)(H:∀ i∈s,Brush j (v i) D (f i) u) : Brush j (∑ i∈s,v i) D (fun z=>∑ i∈s,f i z) u := Brush.spree s f v hd H
local notation "b'"=> gStep β
local notation "Δ"=>Plateau.chopWind P K p O x U Q hx hO F h H H₀ i j k (gStep β) D n
local notation "Δ'"=>Plateau.chopCut U B i j k (gStep β) D A₁ y w -- check

def coil (i:ι) (k:ℕ) (β:ℝ) (n:Side) (x':Positions (Primary n G)) := ∑ j∈ Finset.range (k+1), (gStep β)^j *(topiary P K p O x U Q hx hO F h j i n (bend (gStep β) x')-(R j i).table n (bend (gStep β) x'))
local notation "Ξ" => coil P K p O x U Q hx hO F h (R:=R) i k β n
include he hn hu ha hy hk hD hX
lemma onWind : Brush j (Δ) y⁻¹ (S (Ξ)) X:= by
 let b:=b'; have hb:= gS β he |>.1; let f(r:ℕ) (t:E) := b^r*(V0 r i n (bend b t) -(W) i r n (bend b t)); let F₁(r:ℕ):= S (f r); have heq : S (Ξ)=(fun z=> ∑ r∈Finset.range (k+1), F₁ r z):= by ext1 x; unfold Shellac.off coil F₁; simp_rw [PhysicalNext.Repeat.Shellac.off,Pi.sub_apply,Finset.sum_sub_distrib]; rfl
 rw [heq]; have hb' : 0<b := hb; unfold chopWind; refine Brush.spree _ F₁ _ (inv_nonneg.mpr ha.le) ?_; intro r hr; have hv:= H₀.forms r (by rw [mem_range] at hr; omega); let g:= fun s:E=> V0 r i n (bend b s)-(W) i r n (bend b s); let μ:= H₀.dust r i n * dearth (H₀.tam r) n; let G₁:=tollS D j ((μ * (1+b⁻¹)^(r+2)) * Rail.mantle j (r+2) *2^(r+2)); let Φ(z:E)(h:‖z‖≤y):Brush j (b^r*G₁) y⁻¹ (f r) z:= by -- proof let
     rw [show b^r*G₁=‖b^r‖*G₁ from congr_arg (·* G₁) (Real.norm_of_nonneg (pow_nonneg hb'.le r)).symm]; refine ((brushLens (pricedBend (hv.awake i|>.2 n hn) hb') z h hy hu hD j).climb le_rfl ((one_le_inv₀ ha).2 hy.le)).smul (b^r)
 have h0:= Φ 0 (norm_zero.trans_le ha.le); rw [mul_two]; exact (Φ X hX).separating ((Brush.certified h0.pos _).climb h0.bound le_rfl)
include hA hj
omit hn in
lemma onPeal : Brush j (Δ') y⁻¹ (S (outlay (T:=S') n i b' k - peal S' i b' w k n)) X:= by
 let b := b'; let U(e:ℕ)(r:Fin (e+1)):= S' e r i; let f(l:ℕ)(r:Fin (l+1)) x := played (T:=S') i b l k r x - (ratioW b l (r.val+2))* speak (crop w ∘ U l r) n x; let F₁(l:ℕ) (r: Fin (l+1)):= S (f l r)
 rw [show (S (outlay (T:=S') n i b' k - peal S' i b' w k n))=(fun u=> ∑ l∈ Finset.range (k+1),∑ r: Fin (l+1), F₁ l r u) from ?_];
 · unfold chopCut; refine Brush.spree _ (fun l u=> ∑ r:Fin (l+1), F₁ l r u) _ (inv_nonneg.mpr ha.le) ?_; intro l hl; refine Brush.spree Finset.univ (F₁ l) _ (inv_nonneg.mpr ha.le) ?_; intro r _; have hℓ:=Finset.mem_range.mp hl; obtain ⟨h₀,H⟩:= B.birth l (by omega) r; let A:=U l r; rw [show F₁ l r= S (ratioW b l (r.val+2) • (blockTaylor (k-l+(r.val+2)) (speak A n) - speak (crop w ∘ A) n)) from (by unfold F₁; apply congr_arg; funext i; exact (mul_sub ..).symm)]; exact cuts ha hy hu hD X hX A h₀ (H.2 i|>.1) hA b (gS _ he|>.1) w l k (by have hx:=r.isLt; omega)
 · ext1 v; simp only [F₁,f,Shellac.off,Pi.sub_apply,outlay,peal]; simp_rw [sum_sub_distrib]; rfl
local notation "Σ₀"=> Plateau.paid_corner P K O J F₀ ρ l₀ β (g i) k
local notation "τ"=> peal S' i b' w k n
local notation "Ω"=> edges B' q D (Λ₀ i) (g i) y k
-- open Set
include B hV hS hJ hv hp hG hU hT
lemma crust : Brush j (β* (Ω).1 + (Ω).2 + Δ + Δ') y⁻¹ (S (Σ₀ - τ)) X:= by
 let s:= V i; let f:=staff q s n; let m:=drift q s (g i) n; let A:=β • (f-blockTaylor (k+2) f); let D₂:=m-blockTaylor k m; let G₁:= outlay (T:=S') n i b' k; let H₁ := Local.Pure.script F₀ J O ρ β l₀ k; let F' := (Σ₀); let F₁(x':E):= ∑ j∈Finset.range (k+1), b'^j * topiary P K p O x U Q hx hO F h j i n (bend b' x');
 have heq : F' = H₁ + β • f + m:=by unfold F' Plateau.paid_corner; -- rw hJ hv might all occurrences of J.high in H₁ unaffected
                                       rw [hJ,hv]
 have hp':= lit (n:=n) hS i b' k hk (gS _ he|>.1); have heq' : S (Σ₀) = S A+ S D₂ + S Ξ+ S G₁:= by
    change S F' = _; rw [heq, off_ya,off_ya,show S H₁=S F₁ from sky P K p O x U Q hx hO F h hn J hU hT F₀ l₀ hp k he,← show S _ = S G₁ from hp'];
    -- want identity at all
    have hh(u:E): F₁ u+ β*f u+ m u= A u+D₂ u+ Ξ u + (∑ j∈ Finset.range (k+1), b'^j* ((W) i j n (bend b' u)+ Stipend q s (g i) j n (bend b' u))) +β*f 0:=by -- F_eta rewrite
       let u' j:= Stipend q s (g i) j n (bend b' u); let w j:= (W) i j n (bend b' u); unfold F₁ A D₂ coil; simp_rw [mul_sub,mul_add,sum_sub_distrib,sum_add_distrib]; have he:=fixedS q _ (g i) (hV i) hG u k (β:=β) («he»); simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]; -- inspect type align v
       dsimp only [s,f,m]; linarith only [he]
    ext1 u; have ht:= hh u; have he:=hh 0; unfold Shellac.off; simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at *; linarith only [ht,he] -- he may name shadow
 let H' := corners q s (g i) (hV i) ha hy hu hD X hX B' k hj; have ht:S A= β • (S (f-blockTaylor (k+2) f)):= off_sc ..
 rw [skirt, heq']; change Brush j _ _ (_ +S G₁ - S (τ)) X; rw [add_sub_assoc,← skirt,ht]; refine ((((?_: Brush j (β*(Ω).1) y⁻¹ _ X).gathering H'.2).gathering (onWind P K p O x U Q hx hO F h hn H H₀ hk he ha hy hu hD X hX)).gathering (onPeal U B hk hj he ha hy hu hD X hX hA)); rw (occs:=.pos [1]) [← Real.norm_of_nonneg he.le]; exact H'.1.smul _
end know
end YM.AllOrder.Plateau
