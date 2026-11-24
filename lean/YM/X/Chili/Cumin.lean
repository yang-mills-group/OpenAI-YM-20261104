import YM.X.Chili.Jam
/-!
# program preservation under opposite leg shutters and starsplit Green action. For mixed Wick polynomial evaluation along ANY honest exterior. finite sector at one aperture.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Clove
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Stems Fielding Print Braid Grow Haze MvPolynomial Finset LiftMark Tensor Ocean
open scoped Topology ContDiff BigOperators Classical
variable {q : ℕ+} (hq:1<q.val) {k m n d w:ℕ} {G:Gauge} {R T':ℝ}
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "Q" => (fun i:ℕ=> flow G (side q i))
variable {p s:Deck G} {A:ℕ→ Brush G}{B: Rich G}
def ann (q:ℕ+)(b:Bool)(f:Fan G) (p: Deck G): Deck G:= fun i z=> edge (flow G (side q i)) (Stems.com (leadsL (pace b z) f)) (p i z)
lemma ann_add (q:ℕ+)(f:Fan G)(b:Bool)(p s: Deck G): ann q b f (p+s)=ann q b f p+ ann q b f s:= by ext1 i; ext1 z; exact map_add (edge _ _) _ _
lemma ann_mul (q:ℕ+)(f:Fan G)(b:Bool)(p s: Deck G): ann q b f (p*s)= p* ann q b f s + s*ann q b f p:= by ext1 i; ext1 z; exact (edge _ _).leibniz _ _
def daily (q:ℕ+)(f g:Fan G) : Mist ℂ:= fun i z=> ↑(spend (side q i) 0 z f g)
lemma ann_letter (g f:Fan G)(q:ℕ+): ann q true g (fresh false f)= glass (daily q f g):= by
   ext1 i; ext1 z; unfold ann glass daily fresh pace; rw [link,treats_comm, cornered,spent]; simp
include hq in
lemma cost_daily (hr:0≤R)(g f:Fan G)(hg:g∈Reed.grads G k)(hf:f∈Reed.grads G m): Visa q R 0 (-((m+1+(k+1):ℕ):ℤ)) (daily q f g):= by
   unfold daily; rw [show m+1+(k+1)=2+(m+k) by omega]; exact Visa.com (Haze.rooted_bird hq hr (Print.enrolled₂ f g hf hg))
include hq in
lemma jars (hr:0≤R)(g:Fan G)(hg:g∈Reed.grads G k)(h:Jar false G q R m p) : Jar false G q R (k+1+m) (ann q true g p):= by
    induction h with
    | glass l f h=> rw [show ann q true g (glass f)=0 from funext (fun i=> funext fun z=> Derivation.map_algebraMap ..)]; exact Jar.zero _
    | letter x j f p hf hp ih=> rw [ann_mul,ann_letter]; apply Jar.add; rw [show k+1+(x+1+j)=x+1+(k+1+j) by omega]; exact Jar.letter x _ _ _ hf ih;
                                 rw [mul_comm, show k+1+(x+1+j)=x+1+(k+1)+j by omega]; exact jar_glass _ (cost_daily hq hr g f hg hf) hp
    | add h p IH Hk=> rw [ann_add];exact IH.add Hk
    | weaken x h ih=> exact ih.weaken (by omega)
def purseK (q:ℕ+)(p s: Deck G): Deck G:= fun i z=> hit (flow G (side q i)) (p i z) (s i z)
def purseM (q:ℕ+)(p s: Deck G): Deck G:= fun i z=> multi (flow G (side q i)) (p i z) (s i z)
def purse (q:ℕ+)(p s: Deck G) : Deck G:= fun i z=> knot (flow G (side q i)) (p i z) (s i z)
lemma purse_split (q:ℕ+)(p s: Deck G) : purse q p s= p*s+purseK q p s+purseM q p s:= funext fun i=> funext fun z=> m_op ..
lemma glass_hit (q:ℕ+)(f:Mist ℂ) (p:Deck G): purseK q p (glass f)=0:= by funext i z;exact Derivation.map_algebraMap ..
lemma glass_M (q:ℕ+)(f:Mist ℂ)(p:Deck G): purseM q p (glass f)=0:= by
   funext i z; let s:= f i z; let g:= flow G (side q i); change multi g _ (C s)=0; rw [multi,hit_c,sub_zero,pcomm,pc, mul_comm _ (C s),C_mul',sub_self]
lemma letter_hit (q:ℕ+)(p s:Deck G)(f: Fan G): purseK q p (fresh true f*s)=fresh true f * purseK q p s + ann q true f p * s:= by ext1 i; ext1 z; unfold purseK ann; rw [Pi.mul_apply,Pi.mul_apply,Derivation.leibniz]; simp only [fresh,Pi.add_apply,Pi.mul_apply, smul_eq_mul, hit_glyph];rw [mul_comm (s i z)]
lemma letter_M (q:ℕ+)(p s:Deck G)(f:Fan G) : purseM q p (fresh true f*s)= fresh true f * purseM q p s + purseK q (ann q true f p) s + purseM q (ann q true f p) s:= by ext1 i; ext1 z; exact mstep ..
include hq
lemma mixed_gr (hr:0≤R)(ht:R<T')(h:Tide q T' A)(he:Grasp B)(hb:Fill (gate q T') (fun i=> epsilon q i^(d+1)) d 0 A (emerge q B))(hz:Jar false G q R n p)(hp:Jar true G q R m s) : Grove q R A B d (n+m) (purseK q p s) ∧ Grove q R A B d (n+m) (purseM q p s):= by
    induction hp generalizing n p with
    | glass k f hf=> rw [glass_hit,glass_M]; exact ⟨Submodule.zero_mem (grove q R A B d _),Submodule.zero_mem (grove q R A B d _)⟩
    | letter k m f s hf hp IH=>
       have hZ:= jars hq hr f hf hz; obtain ⟨hx,hp'⟩:= IH hz; obtain ⟨hu,hv⟩:= IH hZ
       let u:=k+1; have he': n+(u+m)=u+(n+m):= by omega
       have he'': n+(u+m)=u+n+m:= by omega
       let w:=n+(u+m); let F:=grove q R A B d w; rw [letter_hit,letter_M]
       have hc:= (Jar.fume f hf (b:=true) (q:=q) (R:=R)).read hq hr ht h he hb; change _∈F ∧ _ ∈ F
       constructor; · exact F.add_mem ((by unfold F w; rw [he']; exact (hc.mul hq hr he hx))) (by unfold F w; rw [he'']; exact ((hZ.read hq hr ht h he hb).mul hq hr he (hp.read hq hr ht h he hb)))
       exact F.add_mem (F.add_mem (by unfold F w; rw [he']; exact (hc.mul hq hr he hp')) (by unfold F w; rw [he'']; exact hu)) (by unfold F w; rw [he'']; exact hv)
    | add x y IH Hp=> obtain ⟨u,v⟩:= IH hz; obtain ⟨e,l⟩:= Hp hz;
                       rename_i r s m;
                       rw [show purseK q p (r+s)=purseK q p r+purseK q p s from funext (fun t=>funext fun z=> map_add (hit _ _) ..), show purseM q p (r+s)=purseM q p r+purseM q p s from funext (fun t=>funext fun z=>madd₀ ..)]; exact ⟨Submodule.add_mem (grove q R A B d _) u e,Submodule.add_mem (grove q R A B d _) v l⟩
    | weaken x hx ih=> obtain ⟨hs,hg⟩:= ih hz; exact ⟨hs.weaken hq hr (by omega),hg.weaken hq hr (by omega)⟩
end YM.PositionX.Clove
