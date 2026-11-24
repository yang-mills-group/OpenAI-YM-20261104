import YM.Contacts.Tempo.Dire
import YM.Contacts.Tempo.Fencible
namespace YM.Contacts.Tempo
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
open Harrier Harrier.Transfer Parcel Planned.PrimaryIntegral295
open Cartons Tensor Place Carrier MultiNext.SignedSource Pattern Barrage Barrage.Reserve.Oasis Analysis
variable {A: Ink G h M} {S:Boom} {e:Parcel G}{s:Parcel.Step}{K j':ℕ}
namespace Grounds
variable (T:Grounds A e S s K k D ζ) {x:Dye G}
local notation "Γ" => terrain ζ (Dye G)
local notation "Η" => terrain (2*ζ) (Dye G)
local notation "η" => bath ζ k (Dye G)
local notation "τ" => hop e s M h
local notation "R" => play h M e s
variable {F P:Sketch G}{V:Badge A.prism→Sketch G}{v:Badge A.prism}
local notation "ℒ" => (2*ζ:ℝ≥0)
variable {m:κ→ℕ}{P Q Y:κ→ℕ→ Sketch G}{C:κ→ Sketch G}
def chord [AddCommGroup X](P:κ→ℕ→X):ℕ→κ→ℕ→X
    | 0=> P
    | j+1=>fun p i=> chord P j p (i+1)-chord P j p i
abbrev today (Z:κ→ Sketch G)(e:Parcel G)(s:Parcel.Step)(M h:ℕ)(n:ℕ): κ→ℕ→ Sketch G:= chord (fun p=>play h M e s (Z p)) n
def Leader (P: κ→ℕ→Sketch G)(M D:ℕ)(ζ:ℝ≥0)(x:Dye G):Prop:= ∀ p i, Living x M D (P p i) ζ
local notation "L" => Living x M D
-- mismatch δ_n
abbrev glitch (P:κ→ℕ→Sketch G)(e:Parcel G)(s:Parcel.Step)(M h:ℕ)(p:κ)(i:ℕ) :Sketch G:= P p (i+1)-hop e s M h i (P p i)
local notation "δ" => today C e s M h
abbrev rentF (P:κ→ℕ→Sketch G)(Z:Pulse.Range (Node (Dye G)))(x:Dye G)(D i r:ℕ): κ→ℕ→ℝ→Prop:= fun p j=>Issued Z D x (P p j) i r
lemma iss_minus (h: Issued η D x (P p n) i r b)(ht:Issued η D x (Q p n) i r c): Issued η D x ((P p n)-(Q p n)) i r (b+c):= ⟨before_sub x h.1 ht.1,w_sub h.2 ht.2⟩
lemma iss_minus' {Z:Pulse.Range (Node (Dye G))}{P Q: Sketch G}(h: Issued Z D x P i r b)(ht:Issued Z D x Q i r c):Issued Z D x (P-Q) i r (b+c):=⟨before_sub x h.1 ht.1,w_sub h.2 ht.2⟩
lemma rent_raise :Rising (rentF Q η x D i r):= fun _ _ _ _ hx h=> issued_mon h hx
local notation "₹" => Road m
local notation "Ψ★" => Fade m
lemma Roads_sub (h:Road m (rentF P η x D i r))(he:Road m (rentF Q η x D i r)): Road m (rentF (P-Q) η x D i r):= by apply Road.up (h.joint he rent_raise rent_raise) (c:=2) _ (by positivity); intro p j b hb ht; change Issued η D x _ i r _; exact (two_mul b).symm ▸ iss_minus' ht.1 ht.2
lemma shades_sub (h:Ψ★ (rentF P η x D i r))(he:Ψ★ (rentF Q η x D i r)): Ψ★ (rentF (P-Q) η x D i r):= by apply Fade.up (h.joint he rent_raise rent_raise) (c:=2) _ (by positivity); intro p j b hb ht; change Issued η D x _ i r _; exact (two_mul b).symm ▸ iss_minus' ht.1 ht.2
lemma shades_add (h:Ψ★ (rentF P η x D i r))(he:Ψ★ (rentF Q η x D i r)): Ψ★ (rentF (P+Q) η x D i r):= by apply Fade.up (h.joint he rent_raise rent_raise) (c:=2) _ (by positivity); intro p j b hb ht; change Issued η D x _ i r _; exact (two_mul b).symm ▸ ⟨before_add ht.1.1 ht.2.1,w_add ht.1.2 ht.2.2⟩
lemma living_chord (hp:Leader P M D ζ x): Leader (chord P i) M D ζ x:= by induction i with|zero=>exact hp|succ j ih=> exact fun p i=> (ih p _).sub (ih p i)
lemma rent_chord (hp: Road m (rentF P η x D i r)): Road m (rentF (chord P j) η x D i r):= by induction j with|zero=>exact hp|succ j ih=> exact Roads_sub (P:=fun p i=> chord P j p (i+1)) (ih.shift rent_raise 1) ih
-- small.F (`Ω-opacity`) for already-purchased portals. For mismatch induction.
include T
lemma present_formula {F Q:Sketch G}(hp:Living x M D F (2*ζ))(he:Living x M D Q (2*ζ)) : τ n (F-Q)= τ n F-τ n Q:= by apply eq_sub_of_add_eq; rw [← means_add T.lic T.steps x h (T.in_path n) ((hp.sub he).lower T.lic.down) (he.lower T.lic.down), sub_add_cancel] -- notation mismatch
lemma leaderDollar (hc:∀ x', Living x M D (C x') (2*ζ)):Leader (δ j) M D (2*ζ) x:= living_chord (fun v i=> T.own (hc v) i)
lemma leaderGlitch (hx:Leader P M D (2*ζ) x):Leader (glitch P e s M h) M D (2*ζ) x:= fun p i=> (hx p _).sub (T.roof ((hx p i).lower T.lic.down))
variable (hi:i≤K)(hr:r≤M+i)
include hi hr
lemma spark (h₀:Leader P M D (2*ζ) x) (hP: ₹ (rentF P η x D i r)) : Ψ★ (fun p n=> Issued η D x (τ (n+1) (P p n)-τ n (P p n)) i r):= by -- overlap m-mile
   obtain ⟨a,ha,H⟩:=Transfer.whole_bill (D:=D) T.lic T.steps x T.south hi h hr; let q:=fit_spare (2*ζ) ζ k T.lic.emit_lt; have hq:0≤q.choose:= zero_le_one.trans q.choose_spec.1;
   refine Road.up hP (c:=q.choose*a) (?_) (mul_nonneg hq ha); intro p n b hb hx; let u:=P p n; let v:=round s n; let Z:=Transfer.mean e; have hg:= (H u ((h₀ p n).lower T.lic.down) b hb (issued_down hx)).2 [s] [] v (T.in_path 1) OK.nil (T.in_path _); have hv: v++[s]=round s (n+1):= by unfold v round; rw [ List.replicate_add]; rfl -- note replicate?
   rw [hv,List.append_nil] at hg; let z:=a*b*tint n; have ht: mileage v=tint n:= by unfold v round tint mileage; rw [List.length_replicate];
   rw [ht] at hg; let K':=τ (n+1) u-τ n u; have hZ':Issued Η D x K' i r z:=hg; let hq':Issued η D x K' i r (q.choose*z):= ⟨fun i j ht=> spa_weight T.lic.light (hZ'.1 i j ht),spa_weight T.lic.light hZ'.2⟩; refine issued_mon hq' (?_); unfold z; exact le_of_eq (by ring)
lemma fetching (hx:∀ p,Living x M D (C p) (2*ζ))(hP: ₹ (rentF (fun p=> R (C p)) η x D i r)) : Ψ★ (rentF (glitch (δ j) e s M h) η x D i r):= by
    induction j with|zero=> exact Fade.by_zero rent_raise (fun p n=> by let x':= C p; change Issued _ _ _ (τ n (R x' n)-τ n (R x' n)) i r 0; rw [sub_self]; exact ⟨fun _ _ _=> w_zero,w_zero⟩)|succ j ih=>
    let P:=δ j; let G:= glitch P e s M h; let H:=δ (j+1); let Y(p:κ)(n:ℕ):= P p (n+1); have heZ:Leader P M D (2*ζ) x:= T.leaderDollar hx; let X (p:κ)(n:ℕ):=τ (n+1) (Y p n)-τ n (Y p n); have h':glitch H e s M h=((fun p n=>G p (n+1))-G)+X:= by
       funext p n; change (P p (n+1+1)-Y p n) - τ n (Y p n-P p n) = ((P p (n+1+1)-τ (n+1) (Y p n))-(Y p n-τ n (P p n)))+X p n; unfold X; rw [present_formula T (heZ p _) (heZ p _)]; abel
    rw [h']; apply shades_add; exact shades_sub (P:=fun p n=> G p (n+1)) (ih.shift rent_raise 1) ih; apply spark T hi hr (P:=Y) (fun p i=>heZ p _); exact (rent_chord hP (j:=j)).shift rent_raise 1
end Grounds
end
end YM.Contacts.Tempo
