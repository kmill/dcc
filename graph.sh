i=${1%.*}
./dcc -t lowir $1 | dot -T pdf > $i.pdf
./dcc -t lowir --debug $1 | dot -T pdf > $i.2.pdf
./dcc -t midir $1 | dot -T pdf > $i.3.pdf
evince $i.pdf &
evince $i.2.pdf &
evince $i.3.pdf
