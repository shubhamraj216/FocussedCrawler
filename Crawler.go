package main

import (
	"os"
	"fmt"
	"log"
	"time"
	"math"
	"sync"
	// "bufio"
	"regexp"
	"context"
	"strings"
	"strconv"
	"net/http"
	"io/ioutil"
	"container/heap"
	"golang.org/x/net/html"
	"github.com/goware/urlx"
	"github.com/samclarke/robotstxt"
	"github.com/PuerkitoBio/goquery"
	"go.mongodb.org/mongo-driver/bson"
	"go.mongodb.org/mongo-driver/mongo"
	"github.com/fluhus/gostuff/nlp/wordnet"
	"go.mongodb.org/mongo-driver/mongo/options"
	"go.mongodb.org/mongo-driver/bson/primitive"
)

type Iter chan int

func Count() Iter {
	c := make(Iter)
	i := 0
	go func() {
		for ; true; i++ {
			c <- i
		}
	}()
	return c
}

// UI => Url Info
type UI struct {
	hyperlink  string
	hypertext  string
	depth      int
	num_par    int
	parent_cos float64
	score      float64
	index      int
}

// Record in DB
type Record struct {
	ID      primitive.ObjectID `bson:"_id,omitempty"`
	keyword string        	   `bson:"keyword,omitempty"`
	url     []Url         	   `bson:"url,omitempty"`
}

// Inserted Url type
type Url struct {
	address string `bson:"address,omitempty"`
	freq 	int    `bson:"freq,omitempty"`
}

// Implement Priority Queue
type PriorityQueue []*UI

func (pq PriorityQueue) Len() int { return len(pq) }
func (pq PriorityQueue) Less(i, j int) bool {
	if pq[i].score == pq[j].score {
		return true
	}
	return pq[i].score > pq[j].score
}
func (pq *PriorityQueue) Push(x interface{}) {
	n := len(*pq)
	item := x.(*UI)
	item.index = n
	*pq = append(*pq, item)
}
func (pq *PriorityQueue) Pop() interface{} {
	old := *pq
	n := len(old)
	item := old[n-1]
	old[n-1] = nil // avoid memory leak
	item.index = -1
	*pq = old[0 : n-1]
	return item
}
func (pq PriorityQueue) Swap(i, j int) {
	pq[i], pq[j] = pq[j], pq[i]
	pq[i].index = i
	pq[j].index = j
}
func (pq *PriorityQueue) Update(item *UI, par_cos float64) {
	item.score = NewScore(item.score, item.parent_cos, par_cos, item.num_par)
	item.num_par = item.num_par + 1
	item.parent_cos = par_cos
	heap.Fix(pq, item.index)
}

var URLS_PQ = make(PriorityQueue, 0)

var SYNONYM = make(map[string][]string)

const WORDNET = "./wordnet"

var EXISTS = struct{}{}

var VISITED_URLS = map[string]*UI{}
var SVU = make(map[string]struct{}) // short visited urls
var COUNTER = Count()
var COUNTERX = Count()
var MAX = 1 << 30
var QUERY string
var DOCUMENTS_WITH_QUERY = make(map[string]int)
var TOTAL_DOCUMENTS = 114000000000.0
var N int
var BASE_GOOGLE_URL = "https://www.google.com/search?q="
var BASE_PARENT = "https://www.google.com"

var ctx context.Context

func get_synonyms() {
	queries := strings.Split(QUERY, " ")

	wn, e := wordnet.Parse(WORDNET)
	if e != nil {
		fmt.Println(e)
	}

	for i := 0; i < len(queries); i++ {
		slice := make([]string, 0)
		set := make(map[string]struct{})
		for _, idx := range []string{"a", "n", "r", "v"} {
			for _, POS := range wn.Search(queries[i])[idx] {
				for _, value := range POS.Word {
					if _, ok := set[value]; !ok {
						slice = append(slice, value)
						set[value] = EXISTS
					}
				}		
			}
		}
		SYNONYM[queries[i]] = slice
	}
}

func NewScore(old_score float64, old_cos float64, new_cos float64, num_par int) float64{
	old_score = old_score / old_cos

	cos_avg := (old_cos * float64(num_par) + new_cos) / float64(num_par + 1.0)

	return old_score * cos_avg
}

func allowed_to_crawl(url string, host string, scheme string) bool {
	if host == "www.google.com" {
		return true
	}

	if host == "" || scheme == "" {
		return false
	}

	RobotURL := scheme + "://" + host + "/robots.txt"
	robots, _ := robotstxt.Parse("", RobotURL)

	allowed, _ := robots.IsAllowed("*", url)

	return allowed
}

func mime_type_okay(url string, res *http.Response) bool{
	ext := url[len(url) - 3 :]

	cond := (ext == "img" || ext == "pdf" || ext == "mp4" || ext == "mp3")

	if cond {
		return false
	}

	mime_ignore := []string{"audio/wav", "audio/midi", "audio/mpeg3", "audio/mp4",
	"audio/x-realaudio", "video/3gp", "video/avi",
	"video/mov", "video/mp4", "video/mpg", "video/mpeg",
	"video/wmv", "text/css", "application/x-pointplus",
	"application/pdf", "application/octet-stream",
	"application/x-binary", "application/zip",
	"application/pdf"}

	contentType := res.Header.Get("Content-Type")
	if contentType == "" {
		return true
	}	
	cType := strings.Split(contentType, ";")[0]

	for _, v := range mime_ignore {
		if v == cType {
			return false
		}
	} 
	return true
}

func get_Content_Length(URL string, res *http.Response) string {
	url, _ := urlx.Parse(URL)

	host_url := url.Host
	scheme := url.Scheme

	cond := allowed_to_crawl(URL, host_url, scheme) && mime_type_okay(URL, res)

	if cond {
		tr := &http.Transport{
			MaxIdleConns:       10,
			IdleConnTimeout:    30 * time.Second,
			DisableCompression: true,
		}
		req, _ := http.NewRequest("GET", URL, nil)
		req.Header.Add("Accept-Encoding", "gzip")
		client := &http.Client{Transport: tr}
		res, err := client.Do(req)
		if err != nil {
			log.Fatal(err)
		}
		
		return res.Header.Get("Content-Length")

	} else {
		return ""
	}
}

func cosine_score(URL string, doc *goquery.Document, res *http.Response) float64 {
	query_freq_in_doc := make(map[string]float64)
	size := get_Content_Length(URL, res)
	q := strings.Split(QUERY, " ")
	body := strings.ToLower(doc.Find("body").Text())

	compute_cosine := func (query_freq_in_doc map[string]float64, D int) float64 {
		compute_first_term := func (q string) float64 {
			return math.Log(1.0 + (TOTAL_DOCUMENTS/float64(DOCUMENTS_WITH_QUERY[q])))
		}

		compute_second_term := func (q string) float64 {
			if _, ok := query_freq_in_doc[q]; !ok {
				return 0
			} else if query_freq_in_doc[q] == 0 {
				return 0
			} else {
				return 1 + math.Log(query_freq_in_doc[q])
			}
		}

		res := 0.0

		for i := 0; i < len(q); i++ {
			first_term := compute_first_term(q[i])
			second_term := compute_second_term(q[i])

			doc_size := math.Sqrt(math.Abs(float64(D)))
			
			if doc_size != 0 {
				res += (first_term * second_term) / doc_size
			}
		}

		return res
	}

	
	for i := 0; i < len(q); i++ {
		var total_count float64 = 0
		var synonym_total_count float64 = 0

		if size != "" {
			query_count := strings.Count(strings.ToLower(body), strings.ToLower(q[i]))
			total_count += float64(query_count)

			for _, value := range SYNONYM[q[i]] {
				synonym_total_count += float64(strings.Count(strings.ToLower(body), strings.ToLower(value)))
			} 

			synonym_total_count *= 0.5
			total_count += synonym_total_count
			query_freq_in_doc[q[i]] = total_count
		} else {
			query_freq_in_doc[q[i]] = total_count
		}
	}

	D := len(strings.Split(body, " "))

	return compute_cosine(query_freq_in_doc, D)
}

func estimate_score(cos float64, hypertext string, hyperlink string) float64 {
	total_text := len(strings.Split(hypertext, " "))
	total_link_length := len(strings.Split(hyperlink, "/"))
	res  := 0.0

	q := strings.Split(QUERY, " ")
	for i := 0; i < len(q); i++ {
		q_in_hypertext := float64(strings.Count(strings.ToLower(hypertext), strings.ToLower(q[i])))
		q_in_hyperlink := float64(strings.Count(strings.ToLower(hyperlink), strings.ToLower(q[i])))
		q_syn_hyper_count := 0.0
		q_syn_curr_count := 0.0
		
		for _, value := range SYNONYM[q[i]] {
            q_syn_hyper_count += float64(strings.Count(strings.ToLower(hypertext), strings.ToLower(value)))
            q_syn_curr_count += float64(strings.Count(strings.ToLower(hyperlink), strings.ToLower(value)))
		}

		q_in_hypertext *= 1.25
		q_in_hyperlink *= 1.25
        q_syn_hyper_count *= 0.5
        q_syn_curr_count *= 0.5

        // idf_for_all := math.Log(TOTAL_DOCUMENTS/DOCUMENTS_WITH_QUERY)

		q_divide_hyper_text := 0.0  // tf
		q_syn_divide_hyper_text := 0.0
        if total_text != 0 {
            q_divide_hyper_text = float64(q_in_hypertext) / float64(total_text)  // tf
            q_syn_divide_hyper_text = (q_syn_hyper_count / float64(total_text))
		}

		q_divide_curr_link := 0.0
		q_syn_divide_curr_link := 0.0
        if total_link_length != 0 {
            q_divide_curr_link = float64(q_in_hyperlink) / float64(total_link_length)
            q_syn_divide_curr_link = q_syn_curr_count/float64(total_link_length)
		}

        res += (q_divide_hyper_text + q_divide_curr_link +
                q_syn_divide_hyper_text + q_syn_divide_curr_link)
	}
	score := res + cos
	return score
}

func get_child_links_from_page(wg *sync.WaitGroup, db *mongo.Database, URL string, depth int) {
	defer wg.Done()

	urls_list_info := make(PriorityQueue, 0)
	res, err := http.Get(URL)
	if err != nil {
		fmt.Println("SKipping")
		return
	}

	defer res.Body.Close()

	// Get the response body as a string
	dataInBytes, err := ioutil.ReadAll(res.Body)
	pageContent := string(dataInBytes)
	
	// clear head and script tags
	pageContent = removeIllegalTags(pageContent)
	
	node, err := html.Parse(strings.NewReader(pageContent))

	if err != nil {
		log.Println(err)
		return
	}
	doc := goquery.NewDocumentFromNode(node)
	if err != nil {
		fmt.Println("Skipping")
		return
	}

	// doc, err := goquery.NewDocumentFromReader(res.Body)
	// if err != nil {
	// 	fmt.Println("Skipping")
	// 	return
	// }

	par_cos := cosine_score(URL, doc, res)
	parsed_URL, _ := urlx.Parse(URL)

	go extractKeywords(doc.Text(), db, URL)

	doc.Find("a").Each(func(i int, s *goquery.Selection) {
		href, exists := s.Attr("href")
			
		if exists && href != "" {
			child_depth := depth

			// Modify the direct links
			if href[0] == '/' {
				href = parsed_URL.Host + href
			}

			// Get the text: <a>text</a>
			var text string
			text = s.Text()

			// Normalise the url
			parsed_url, _ := urlx.Parse(href)
			url, _ := urlx.Normalize(parsed_url)

			if parsed_url == nil {
				goto end
			}

			// ignore if advertisement link or refer-to-post link
			if strings.Contains(url, "&via=") || 
			   (strings.Contains(url, "title=") && strings.Contains(url, "&url=")) || 
			   (strings.Contains(url, "text=") && strings.Contains(url, "&u=")) || 
			   (strings.Contains(url, "title=") && strings.Contains(url, "&u=")) || 
			   (strings.Contains(url, "text=") && strings.Contains(url, "&url=")) {
				goto end
			}

			if _, ok := VISITED_URLS[url]; ok {
				if _, okp := VISITED_URLS[URL]; okp {
					goto end
				}
				if VISITED_URLS[url] == nil {
					goto end
				}
				URLS_PQ.Update(VISITED_URLS[url], par_cos)
				goto end
			}

			// fmt.Println(parsed_URL.Host, parsed_url.Host)
			if parsed_url.Host == parsed_URL.Host {
				child_depth++

				if child_depth > 5 {
					goto end
				}
			}

			url_info := UI{
				hyperlink:  url,
				hypertext: text,
				depth:      child_depth,
				parent_cos: par_cos,
				score:      estimate_score(par_cos, text, url),
				index:      <-COUNTER,
			}
			// Append url, hypertext, depth and score in the url_list
			if url_info.score == url_info.score  {
				heap.Push(&urls_list_info, &url_info)
			}
		}
		end:
	})

	counter := 20
	for urls_list_info.Len() > 0 && counter > 0 {
		item := heap.Pop(&urls_list_info).(*UI)
		short := get_short(item.hyperlink)
		if _, ok := SVU[short]; !ok {
			heap.Push(&URLS_PQ, item)
			VISITED_URLS[item.hyperlink] = item
			SVU[short] = EXISTS
			// fmt.Println(counter, ": ", item.score, " ", item.hyperlink)
			counter--;
		}
	}

}

func get_short(url string) string {
	res := ""
	c := 0
	for i := 0; i < len(url); i++ {
		if url[i] == '/' {
			c++;
		}
		if c == 7 {
			break;
		}
		res += string(url[i])
	}
	return res
}

func get_seeds_from_google(URL string, start_regex string, google bool, depth int, top_search bool) []UI {
	google_ignore := []string{
		"Google", "Videos", "Books", "News", "Images", "Maps", "Learn why",
		"Shopping", "Search tools", "Past hour", "Past 24 hours", "webcache",
		"Past week", "Past month", "Past year", "Verbatim", "Next >", "watch",
		"Learn more", "Sign in", "Settings", "Privacy", "Terms", ">", "<",
	}

	// Check if google ignore links
	valid := func(text string) bool {
		for _, v := range google_ignore {
			if strings.Contains(text, v) {
				return false
			}
		}
		return true
	}

	// google search result list
	google_urls_list := make([]UI, 0)
	get_google_results := func(URL string) {
		res, err := http.Get(URL)
		if res == nil || err != nil {
			log.Fatal("Some error occured")
			return
		}

		defer res.Body.Close()

		// Load the HTML document
		doc, err := goquery.NewDocumentFromReader(res.Body)
		if err != nil {
			log.Fatal(err)
		}

		// Select all anchor tags and iterating over them
		doc.Find("a").Each(func(i int, s *goquery.Selection) {
			href, exists := s.Attr("href")
			if exists {
				// Modify the direct links
				if !strings.Contains(href, start_regex) && href[0] == '/' {
					href = BASE_PARENT + href
				}
				
				// Trim the links
				if strings.Index(href, "&sa") > 0 {
					href = href[strings.Index(href, "http") : strings.Index(href, "&sa")]
				}

				// Get the text: <a>text</a>
				var text string
				text = s.Text()

				if valid(text) && !strings.Contains(href, "google.com") {
					// Normalise the url
					parsed_url, _ := urlx.Parse(href)
					url, _ := urlx.Normalize(parsed_url)

					if s.Find("h3").Text() != "" {
						text = s.Find("h3").Text()
					}

					url_info := UI{
						hyperlink:  url,
						hypertext: text,
						depth:      depth + 1,
						num_par:    0,
						parent_cos: float64(MAX),
						score:      float64(MAX),
						index:      <-COUNTER,
					}
					// Append url, hypertext, depth and score in the url_list
					google_urls_list = append(google_urls_list, url_info)
				}
			}
		})
	}

	get_google_results(URL)
	get_google_results(URL + "&start=10")

	return google_urls_list
}

func get_google_search_urls(query string) {
	parsed_url, _ := urlx.Parse(BASE_GOOGLE_URL + query)
	url, _ := urlx.Normalize(parsed_url)

	urls_list_info := get_seeds_from_google(url, "/url?q=", true, 0, true)

	for i := 0; i < len(urls_list_info); i++ {
		if strings.Contains(urls_list_info[i].hyperlink, "wiki") {
			continue
		}
		if _, ok := VISITED_URLS[urls_list_info[i].hyperlink]; !ok {
			heap.Push(&URLS_PQ, &urls_list_info[i])
			VISITED_URLS[urls_list_info[i].hyperlink] = &urls_list_info[i]
		}
	}
}

func Fill_DWQ(r string) {

	url := BASE_GOOGLE_URL + r

    req, _ := http.NewRequest("GET", url, nil)

    req.Header.Add("user-agent", "Mozilla/5.0 Firefox/84.0")

    res, err := http.DefaultClient.Do(req)

	if err != nil {
		fmt.Println(err)
		DOCUMENTS_WITH_QUERY[r] = 0
		return
	}

    defer res.Body.Close()

    doc, _ := goquery.NewDocumentFromReader(res.Body)

    doc.Find("div #result-stats").Each(func(i int, s *goquery.Selection) {
        num := ""
        for _, v := range strings.Split(strings.Split(s.Text(), " ")[1], ",") {
            num += v
        }
		DOCUMENTS_WITH_QUERY[r], _ = strconv.Atoi(num)
    })
}

func focussed() {
	var wg sync.WaitGroup
	for _, v := range strings.Split(QUERY, " ") {
		Fill_DWQ(v)
	}

	get_google_search_urls(QUERY)
	// cosine_list := make([]float64, 0)
	// fo, err := os.Create(QUERY + ".txt")
    // if err != nil {
    //     panic(err)
    // }
    // close fo on exit and check for its returned error
    // defer func() {
    //     if err := fo.Close(); err != nil {
    //         panic(err)
    //     }
	// }()
	
	<-COUNTERX

	//get the database
	db := get_db()

	counts := 0
	for len(URLS_PQ) > 0 && counts < N {
		pop := heap.Pop(&URLS_PQ).(*UI)

		VISITED_URLS[pop.hyperlink] = nil

		wg.Add(1)
		go get_child_links_from_page(&wg, db, pop.hyperlink, pop.depth)
		wg.Wait()
		
		// log_to_file(fo, pop)

		counts++
	}
	fmt.Println(len(URLS_PQ))
}

func main() {
	start_time := time.Now().UTC().Second()

	// fmt.Println("Enter the Query(Space Seperated): ")
	// in := bufio.NewReader(os.Stdin)
	// QUERY, _ = in.ReadString('\n')
	// fmt.Println("Enter No. of pages to crawl: ")
	// fmt.Scan(&N)
	argsWithoutProg := os.Args[1:]
	for i := 0; i < len(argsWithoutProg) - 1; i++ {
		QUERY += argsWithoutProg[i] + " "
	}

	// QUERY = argsWithoutProg[0]
	N, _ = strconv.Atoi(argsWithoutProg[len(argsWithoutProg) - 1])
	fmt.Println((QUERY))
	fmt.Println(N)
	if strings.Contains(QUERY, "\n")  {
		QUERY = QUERY[:strings.Index(QUERY, "\n")]
	}
	QUERY = strings.TrimSpace(QUERY)
	QUERY = strings.ToLower(QUERY)

	get_synonyms()
	focussed()

	end_time := time.Now().UTC().Second()
	fmt.Println(end_time - start_time, "seconds")
}

func log_to_file(fo *os.File, pop *UI) {
	if _, err := fo.Write([]byte("===========================================\n")); err != nil {panic(err)}
	if _, err := fo.Write([]byte("#No: " + strconv.Itoa(<-COUNTERX) + "\n")); err != nil {panic(err)}
	if _, err := fo.Write([]byte("HyperLink: " + pop.hyperlink + "\n")); err != nil {panic(err)}
	if _, err := fo.Write([]byte("HyperText: " + pop.hypertext + "\n")); err != nil {panic(err)}
	if _, err := fo.Write([]byte("Time Now: " + time.Now().String() + "\n")); err != nil {panic(err)}
	if _, err := fo.Write([]byte("Score: " + strconv.FormatFloat(pop.score, 'E', -1, 64) + "\n")); err != nil {panic(err)}
	if _, err := fo.Write([]byte("Average Cosine of Parents: " + strconv.FormatFloat(pop.parent_cos, 'E', -1, 64) + "\n")); err != nil {panic(err)}
	if _, err := fo.Write([]byte("Depth: " + strconv.Itoa(pop.depth) + "\n")); err != nil {panic(err)}
}

func get_db() *mongo.Database {
	clientOptions := options.Client().ApplyURI("mongodb://127.0.0.1:27017")
	ctx := context.TODO()
	client, err := mongo.Connect(ctx, clientOptions)

	if err != nil {
		log.Fatal(err)
	}

	err = client.Ping(ctx, nil)

	if err != nil {
		log.Fatal(err)
	}

	// defer client.Disconnect(ctx)
	fmt.Println("Connected to MongoDB!")

	db := client.Database("shuttle")

	return db
}

func extractKeywords(pageText string, db *mongo.Database, url string) {
	m1 := regexp.MustCompile(`[^a-z^A-Z^\d-_']`)
	pageText = m1.ReplaceAllString(pageText, " ")
	keywords := strings.Fields(pageText)

	query := strings.Split(QUERY, " ")

	a := make([]string, 0)
	for i := 0; i < len(query); i++ {
		a = append(a, query[i])
	}
	for _, elem := range keywords {
		elem = strings.ToLower(elem)
		for i := 0; i < len(query); i++ {
			if query[i] == elem {
				query[i] = a[len(query) - 1]
				query[len(query) - 1] = ""
				query = query[: len(query) - 1]
			}
		}
		keyword, err := db.Collection("keyword").Find(ctx, bson.M{"keyword" : elem})
		if err != nil {
			log.Println(err)
			continue
		}
		var keywordsFiltered []Record
		if err = keyword.All(ctx, &keywordsFiltered); err != nil {
			log.Println(err)
			continue
		}
		if len(keywordsFiltered) == 0 {
			db.Collection("keyword").InsertOne(ctx, bson.D{
				{Key : "keyword", Value : elem},
				{Key : "url" , Value : bson.A{
					bson.D{
						{Key : "address", Value : url},
						{Key: "freq", Value : 1},
					}},
				},
			})
		} else {
			result, err := db.Collection("keyword").UpdateOne(
				ctx,
				bson.M{
					"keyword" : elem,
					"url.address" : url,
				},
				bson.D{
					{"$inc", bson.D{
						{"url.$.freq", 1},
					}},
				},
			)
			if err != nil {
				log.Println(err)
			}
			if result.MatchedCount == 0 {
				db.Collection("keyword").UpdateOne(
					ctx,
					bson.M{
						"keyword" : elem,
					},
					bson.M{
						"$push" : bson.M{
							"url" : bson.M{
								"address" : url,
								"freq" : 1,
							},
						},
					},
				)
			}
		}
	}
	for i := 0; i < len(query); i++ {
		elem := query[i]
		keyword, err := db.Collection("keyword").Find(ctx, bson.M{"keyword" : elem})
		if err != nil {
			log.Println(err)
			continue
		}
		var keywordsFiltered []Record
		if err = keyword.All(ctx, &keywordsFiltered); err != nil {
			log.Println(err)
			continue
		}
		if len(keywordsFiltered) == 0 {
			db.Collection("keyword").InsertOne(ctx, bson.D{
				{Key : "keyword", Value : elem},
				{Key : "url" , Value : bson.A{
					bson.D{
						{Key : "address", Value : url},
						{Key: "freq", Value : 1},
					}},
				},
			})
		} else {
			result, err := db.Collection("keyword").UpdateOne(
				ctx,
				bson.M{
					"keyword" : elem,
					"url.address" : url,
				},
				bson.D{
					{"$inc", bson.D{
						{"url.$.freq", 1},
					}},
				},
			)
			if err != nil {
				log.Println(err)
			}
			if result.MatchedCount == 0 {
				db.Collection("keyword").UpdateOne(
					ctx,
					bson.M{
						"keyword" : elem,
					},
					bson.M{
						"$push" : bson.M{
							"url" : bson.M{
								"address" : url,
								"freq" : 1,
							},
						},
					},
				)
			}
		}
	}
}

func removeIllegalTags(pageContent string) (string) {
	re := regexp.MustCompile("<script.*?</script>")
	temp := ""
	for _, value := range re.Split(pageContent, -1) {
		temp += value
	}
	
	return temp
}