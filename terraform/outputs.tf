# deploy.sh reads both of these to build the connection strings and find the instance
output "db_endpoint" {
  value = aws_db_instance.main.endpoint
}

output "app_ip" {
  value = aws_instance.app.public_ip
}
